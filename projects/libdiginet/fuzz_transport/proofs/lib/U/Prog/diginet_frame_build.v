(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 542 of its 587 lines of code are new or changed and 404 lines of the source are left out. *)
(* proves the UBSan contract of diginet_frame_build (fuzz_transport.ubsan, 0x18260), with its 22 trap branches not taken. *)
(* Modified by Theorem Labs, 2026-10: relocated from libdiginet/fuzz_frame proofs/libdiginet/fuzz_frame/lib/U/Prog/diginet_frame_build.v at 9bd29914ffdef650a37285056a472ff186b4331a to fuzz_transport's images *)
(* Walk of diginet_frame_build (src/diginet_frame.c:93-127 at 835f336c) in fuzz_transport.ubsan,
   0x18260..0x18520, against U/Prog/diginet_frame_build_c.v. The contracts of
   diginet_body_check, memcpy, diginet_sum16 and memset are its hypotheses.
   The two paths into 0x18318 (body_len under 30 or not) and into 0x183c0 (DIGINET_SUM_BODY
   with diginet_sum16, DIGINET_SUM_ZERO without) are joined by the claims K1 and K2. The exits
   with a code under 0 end in err_fin; the three with the frame length (body_len 0, 1 .. 29
   with memset, 30 and more) end in ok_fin. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import diginet_frame_build_c
  diginet_body_check_c memcpy_c diginet_sum16_c memset_c.
Import ListNotations.
Open Scope Z_scope.

(** * Tactics *)

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

(* Decide a branch whose condition the context fixes. *)
Ltac take b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b; [cbv iota | symmetry; unfold_cond; usub; fold_lit_ux; solve_cond_rec]
  end.

Ltac take_by b tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.

(** * Cells of the buffer *)

Lemma rw_cells_split2 : forall m A B cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.

Lemma rw_cells_join2 : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma rw_cb_split : forall m A (k r : nat) l,
  rw_cells rsegs m A [CB (k + r) l] ->
  rw_cells rsegs m A [CB k (firstn k l)] /\ rw_cells rsegs m (A + Z.of_nat k) [CB r (skipn k l)].
Proof.
  intros m A k r l H.
  assert (Hl : length l = (k + r)%nat) by (destruct H as [[[Hl _] _] _]; exact Hl).
  apply (rw_cells_split2 m A (A + Z.of_nat k) [CB k (firstn k l)] [CB r (skipn k l)]); [|cbn; lia].
  eapply rw_cells_rebytes; [exact H| |].
  - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
  - cbn. rewrite !app_nil_r. apply firstn_skipn.
Qed.

(** * The header fields at hp + 4 *)

Lemma hdr_ro : forall m hp send ack retry cmd ncmds,
  0 <= send < 2^32 -> 0 <= ack < 2^32 -> 0 <= retry < 2^16 ->
  bytes_at rsegs m (hp + 4)
    (Z_to_le_bytes 4 send ++ Z_to_le_bytes 4 ack ++ Z_to_le_bytes 2 retry ++ [b8 cmd; b8 ncmds]) ->
  ro_cells rsegs m (hp + 4)
    [C4 (Z_to_bv 64 send); C4 (Z_to_bv 64 ack); C2 (Z_to_bv 64 retry); C1 (b8 cmd); C1 (b8 ncmds)].
Proof.
  intros m hp send ack retry cmd ncmds Hs Ha Hr H. unfold ro_cells, cells_at.
  split; [cbn; tauto|].
  cbn [cells_bytes cbytes app]. unfold le4, le2. rewrite !unsigned_lit by lia. exact H.
Qed.

(** * The stack *)

(* The stack from lo to the 240 bytes below sp after the call: outside the footprint the bytes
   are those of the entry, inside it they are the bytes of the buffer. *)
Lemma stk_rebuild : forall m0 m lo hi a b A n cs,
  stk rsegs m0 lo hi -> munch [(a, b); (A, A + n)] m0 m -> wmono rsegs m0 m ->
  hi <= a -> rw_cells rsegs m A cs -> Z.of_nat (cells_size cs) = n ->
  stk rsegs m lo hi.
Proof.
  intros m0 m lo hi a b A n cs (H1 & H2 & H) Hm Hw Hha [[Hwf Hb] _] Hn.
  destruct Hb as (HA & HAl & Hbi). rewrite cells_bytes_length in HAl by exact Hwf.
  split; [lia|]. split; [lia|]. intros x Hx.
  destruct (H x Hx) as [Hwx (b0 & Hb0)]. split; [apply Hw; exact Hwx|].
  destruct (Z_lt_le_dec x A) as [Lt|Ge]; [| destruct (Z_lt_le_dec x (A + n)) as [Lt2|Ge2]].
  - exists b0. unfold mrd in *. rewrite Hm; [exact Hb0|]. rewrite wa_unsigned by lia.
    cbn [outside]. repeat split; lia.
  - specialize (Hbi (Z.to_nat (x - A))). rewrite cells_bytes_length in Hbi by exact Hwf.
    replace (A + Z.of_nat (Z.to_nat (x - A))) with x in Hbi by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat (x - A))) as [b1|] eqn:E.
    + exists b1. apply Hbi. lia.
    + apply nth_error_None in E. rewrite cells_bytes_length in E by exact Hwf. lia.
  - exists b0. unfold mrd in *. rewrite Hm; [exact Hb0|]. rewrite wa_unsigned by lia.
    cbn [outside]. repeat split; lia.
Qed.

(** * Facts the step tactics do not see *)

(* A fact under keep is out of reach of the step tactics and of lia: the disjointness facts,
   whose disjunctions make lia slow, and the facts on the memory at a fence, moved to the
   current memory with xport. *)
Definition keep (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (keep T) in H.

(* H2: the kept fact H on memory ms, moved to the memory mc of the fence MUf : munch W ms mc,
   WMf : wmono ms mc; tac exposes the disjointness facts the move needs. *)
Ltac xport H H2 MUf WMf tac :=
  pose proof H as H2; unfold keep in H2;
  lazymatch type of H2 with
  | bytes_at ?segs ?ms ?A ?bs =>
      let H' := fresh "X" in
      pose proof (bytes_at_transport segs _ ms _ A bs H2 MUf) as H'; clear H2; rename H' into H2
  | rw_cells ?segs ?ms ?A ?cs =>
      let H' := fresh "X" in
      pose proof (rw_cells_transport segs _ ms _ A cs H2 MUf WMf) as H'; clear H2; rename H' into H2
  | ro_cells ?segs ?ms ?A ?cs =>
      let H' := fresh "X" in
      pose proof (ro_cells_transport segs _ ms _ A cs H2 MUf) as H'; clear H2; rename H' into H2
  | stk ?segs ?ms ?lo ?hi =>
      let H' := fresh "X" in
      pose proof (stk_transport_disjoint segs _ ms _ lo hi H2 MUf WMf) as H'; clear H2; rename H' into H2
  end;
  specialize (H2 ltac:(cbn [disjoint_from]; simpl_sizes; tac; lia)).

(** * Branch conditions *)

(* 0x182c0 .. 0x182cc: snez, seqz, and, bnez of the body_len && !body test. A body address of
   2^64 is in the premises only with body_len 0. *)
Lemma and_test_false : forall body n, (n = 0 \/ 0 < body < 2^64) ->
  negb (bv_eqb (Z_to_bv 64 (Z.land (bv_unsigned (v_sltiu (Z_to_bv 64 body) 1))
                                   (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 n)))))
               (Z_to_bv 64 0)) = false.
Proof.
  intros body n [-> | Hb].
  - replace (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0))) with 0 by (vm_compute; reflexivity).
    rewrite Z.land_0_r. vm_compute. reflexivity.
  - unfold v_sltiu. rewrite (unsigned_lit body) by lia.
    replace (bv_wrap 64 1) with 1 by (vm_compute; reflexivity).
    replace (body <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite (unsigned_lit 0) by lia. rewrite Z.land_0_l. vm_compute. reflexivity.
Qed.

Lemma land3_mod4 : forall x, 0 <= x -> Z.land x 3 = x mod 4.
Proof. intros x Hx. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(** * The buffer in pieces *)

Lemma rw_cb_cut : forall m A B (k n : nat) l,
  rw_cells rsegs m A [CB n l] -> (k <= n)%nat -> B = A + Z.of_nat k ->
  rw_cells rsegs m A [CB k (firstn k l)] /\ rw_cells rsegs m B [CB (n - k) (skipn k l)].
Proof.
  intros m A B k n l H Hk ->. replace n with (k + (n - k))%nat in H by lia.
  destruct (rw_cb_split m A k (n - k) l H) as [H1 H2].
  replace (k + (n - k) - k)%nat with (n - k)%nat in H2 by lia. split; [exact H1 | exact H2].
Qed.

(* The cap bytes at out: the two MACs, the 18 bytes of the header, the body, the padding and
   the rest. *)
Lemma out_split : forall m A (n k : nat) oj,
  (30 + n + k <= length oj)%nat ->
  rw_cells rsegs m A [CB (length oj) oj] ->
  (exists j, rw_cells rsegs m A [CB 6 j]) /\
  (exists j, rw_cells rsegs m (A + 6) [CB 6 j]) /\
  (exists j, rw_cells rsegs m (A + 12) [CB 18 j]) /\
  (exists j, rw_cells rsegs m (A + 30) [CB n j]) /\
  (exists j, rw_cells rsegs m (A + 30 + Z.of_nat n) [CB k j]) /\
  rw_cells rsegs m (A + 30 + Z.of_nat n + Z.of_nat k)
    [CB (length oj - (30 + n + k)) (skipn (30 + n + k) oj)].
Proof.
  intros m A n k oj Hl H0.
  destruct (rw_cb_cut m A (A + 6) 6 _ _ H0 ltac:(lia) ltac:(lia)) as [H1 G1].
  destruct (rw_cb_cut m (A + 6) (A + 12) 6 _ _ G1 ltac:(lia) ltac:(lia)) as [H2 G2].
  destruct (rw_cb_cut m (A + 12) (A + 30) 18 _ _ G2 ltac:(lia) ltac:(lia)) as [H3 G3].
  destruct (rw_cb_cut m (A + 30) (A + 30 + Z.of_nat n) n _ _ G3 ltac:(lia) ltac:(lia)) as [H4 G4].
  destruct (rw_cb_cut m (A + 30 + Z.of_nat n) (A + 30 + Z.of_nat n + Z.of_nat k) k _ _ G4
              ltac:(lia) ltac:(lia)) as [H5 G5].
  assert (E : forall x : list byte, skipn k (skipn n (skipn 18 (skipn 6 (skipn 6 x)))) = skipn (30 + n + k) x).
  { intros x. rewrite !skipn_skipn. f_equal. lia. }
  rewrite E in G5.
  replace (length oj - 6 - 6 - 18 - n - k)%nat with (length oj - (30 + n + k))%nat in G5 by lia.
  split; [eexists; exact H1|]. split; [eexists; exact H2|]. split; [eexists; exact H3|].
  split; [eexists; exact H4|]. split; [eexists; exact H5|]. exact G5.
Qed.

(* The buffer after the writes: the pieces joined, as one block of bytes T. *)
Lemma out_final : forall m A (n k r : nat) cs3 b1 b2 b4 b5 b6 T L,
  rw_cells rsegs m A [CB 6 b1] -> rw_cells rsegs m (A + 6) [CB 6 b2] ->
  rw_cells rsegs m (A + 12) cs3 -> cells_size cs3 = 18%nat ->
  rw_cells rsegs m (A + 30) [CB n b4] -> rw_cells rsegs m (A + 30 + Z.of_nat n) [CB k b5] ->
  rw_cells rsegs m (A + 30 + Z.of_nat n + Z.of_nat k) [CB r b6] ->
  b1 ++ b2 ++ cells_bytes cs3 ++ b4 ++ b5 ++ b6 = T -> (30 + n + k + r)%nat = L ->
  rw_cells rsegs m A [CB L T].
Proof.
  intros m A n k r cs3 b1 b2 b4 b5 b6 T L H1 H2 H3 S3 H4 H5 H6 ET EL. subst T L.
  pose proof (rw_cells_join2 _ _ (A + 30 + Z.of_nat n + Z.of_nat k) _ _ H5
                ltac:(cbn [cells_size csize]; lia) H6) as J5.
  pose proof (rw_cells_join2 _ _ (A + 30 + Z.of_nat n) _ _ H4 ltac:(cbn [cells_size csize]; lia) J5) as J4.
  pose proof (rw_cells_join2 _ _ (A + 30) _ _ H3 ltac:(rewrite S3; lia) J4) as J3.
  pose proof (rw_cells_join2 _ _ (A + 12) _ _ H2 ltac:(cbn [cells_size csize]; lia) J3) as J2.
  pose proof (rw_cells_join2 _ _ (A + 6) _ _ H1 ltac:(cbn [cells_size csize]; lia) J2) as J1.
  pose proof J1 as [[W _] _].
  eapply rw_cells_rebytes; [exact J1 | |].
  - cbn [cells_wf cell_wf]. split; [|exact I].
    pose proof (cells_bytes_length _ W) as L.
    rewrite !cells_bytes_app, !cells_size_app in L. cbn [cells_bytes cbytes cells_size csize] in L.
    rewrite !app_nil_r in L. rewrite L, S3. lia.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

Lemma b8_u64 : forall z, b8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof.
  intros z. unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64. change (Z.of_N 8) with 8. apply mod_mod_pow2. lia.
Qed.

Lemma b8_def : forall z, Z_to_bv 8 z = b8 z.
Proof. reflexivity. Qed.

Lemma b8_zxb : forall b, b8 (bv_unsigned (zxb b)) = b.
Proof. intros b. unfold zxb. rewrite b8_u64. apply b8_bz. Qed.

Lemma swrap_mod : forall n z, 0 <= Z.of_N n -> bv_swrap n z mod 2^(Z.of_N n) = z mod 2^(Z.of_N n).
Proof.
  intros n z Hn. unfold bv_swrap, bv_wrap, bv_modulus.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.

(* A byte of x >> k for a value x that agrees with v below bit w. *)
Lemma b8_shr_agree : forall X v k w, X mod 2^w = v -> 0 <= k -> k + 8 <= w ->
  b8 (Z.shiftr X k) = b8 (v / 2^k).
Proof.
  intros X v k w HX Hk Hw. rewrite Z.shiftr_div_pow2 by lia.
  rewrite <- (b8_div_mod X k w) by lia. rewrite HX. reflexivity.
Qed.

Lemma b8_agree : forall X v w, X mod 2^w = v -> 8 <= w -> b8 X = b8 v.
Proof. intros X v w HX Hw. rewrite <- (b8_mod_w X w) by lia. rewrite HX. reflexivity. Qed.

Lemma sx32_agree : forall v, 0 <= v < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 v)) mod 2^32 = v.
Proof.
  intros v Hv. unfold sx32. rewrite (unsigned_lit v) by lia. rewrite unsigned_lit_wrap.
  rewrite mod_mod_pow2 by lia. rewrite (swrap_mod 32) by lia. apply Z.mod_small. exact Hv.
Qed.

Lemma zx16_agree : forall v, 0 <= v < 2^16 -> bv_unsigned (zx16 (Z_to_bv 64 v)) mod 2^16 = v.
Proof.
  intros v Hv. unfold zx16. rewrite (unsigned_lit v) by lia. rewrite (Z.mod_small v (2^16)) by lia.
  rewrite (unsigned_lit v) by lia. apply Z.mod_small. exact Hv.
Qed.

(* The 18 bytes the stores of 0x18360 .. 0x184a0 write at out + 12. *)
Lemma hdr_bytes : forall N sv send ack retry cmd ncmds,
  0 <= N <= 1484 -> 0 <= sv < 2^16 -> 0 <= send < 2^32 -> 0 <= ack < 2^32 -> 0 <= retry < 2^16 ->
  [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 136)); Z_to_bv 8 (bv_unsigned (Z_to_bv 64 95));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (N + 16))) 8)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (N + 16)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr sv 8)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 sv));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 send))) 24)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 send))) 16)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 send))) 8)));
   Z_to_bv 8 (bv_unsigned (sx32 (Z_to_bv 64 send)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 ack))) 24)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 ack))) 16)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 ack))) 8)));
   Z_to_bv 8 (bv_unsigned (sx32 (Z_to_bv 64 ack)));
   Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (zx16 (Z_to_bv 64 retry))) 8)));
   Z_to_bv 8 (bv_unsigned (zx16 (Z_to_bv 64 retry)));
   Z_to_bv 8 (bv_unsigned (zxb (b8 cmd)));
   Z_to_bv 8 (bv_unsigned (zxb (b8 ncmds)))] =
  put16 0x885f ++ put16 (16 + N) ++ put16 sv ++ put32 send ++ put32 ack ++ put16 retry ++
  [b8 cmd; b8 ncmds].
Proof.
  intros N sv send ack retry cmd ncmds HN Hsv Hs Ha Hr.
  pose proof (sx32_agree send Hs) as XS. pose proof (sx32_agree ack Ha) as XA.
  pose proof (zx16_agree retry Hr) as XR.
  unfold put16, put32. cbn [app].
  repeat match goal with |- context [Z_to_bv 8 ?z] => change (Z_to_bv 8 z) with (b8 z) end.
  rewrite !b8_zxb.
  rewrite (b8_agree _ _ 32 XS) by lia. rewrite (b8_agree _ _ 32 XA) by lia.
  rewrite (b8_agree _ _ 16 XR) by lia.
  rewrite !b8_u64.
  rewrite (unsigned_lit (N + 16)) by lia.
  rewrite !(b8_shr_agree _ _ _ 32 XS) by lia.
  rewrite !(b8_shr_agree _ _ _ 32 XA) by lia.
  rewrite !(b8_shr_agree _ _ _ 16 XR) by lia.
  rewrite !Z.shiftr_div_pow2 by lia.
  replace (N + 16) with (16 + N) by lia.
  replace (b8 95) with (b8 0x885f) by (apply bv_eq; vm_compute; reflexivity).
  replace (b8 136) with (b8 (0x885f / 2^8)) by (apply bv_eq; vm_compute; reflexivity).
  reflexivity.
Qed.

(* The bytes of the buffer are the frame, then the rest of the buffer. *)
Lemma frame_bytes_eq : forall dmac smac bb send ack retry cmd ncmds (z : bool) sv b4 pad rest,
  sv = (if z then 0 else spec_sum bb) -> b4 = bb -> pad = repeat (b8 0) (30 - length bb) ->
  dmac ++ smac ++ (put16 0x885f ++ put16 (16 + Z.of_nat (length bb)) ++ put16 sv ++
     put32 send ++ put32 ack ++ put16 retry ++ [b8 cmd; b8 ncmds]) ++ b4 ++ pad ++ rest =
  build_frame dmac smac send ack retry cmd ncmds bb z ++ rest.
Proof. intros. subst. unfold build_frame. rewrite !app_assoc. reflexivity. Qed.

Lemma nil_of_len : forall (l1 l2 : list byte), length l1 = length l2 -> length l2 = 0%nat -> l1 = l2.
Proof. intros [|x l1] [|y l2] H1 H2; cbn in *; congruence. Qed.

(* Replace the value of register x<k> of the state by v; the first goal is the equation of the
   old value and v. *)
Ltac set_reg_tac k v :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 k)) in
      let R' := eval cbv beta iota delta [tset] in (tset p v R) in
      apply (evt_eq segs Q (MS R F pc fc rv m ro) (MS R' F pc fc rv m ro));
      [ f_equal; repeat match goal with
                 | |- TNode _ _ _ = TNode _ _ _ => f_equal
                 | |- Some _ = Some _ => f_equal
                 end
      | ]
  end.

(* The register leaves of the end state: evars, kept values, then sp and a0 by bv_eq. *)
Ltac fin_regs :=
  unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end;
  try (apply bv_eq; usub; first [lia | vm_compute; reflexivity]).

(* An exit with a code under 0 after the frame is restored: the buffer keeps its bytes. *)
Ltac err_fin FR STa ST0 sp lo BC RWO MUS WMS D :=
  release_frame FR STa (bv_unsigned sp);
  let R := fresh "RWOx" in
  xport RWO R MUS WMS ltac:(unfold keep in D);
  let S0 := fresh "ST0x" in
  xport ST0 S0 MUS WMS idtac;
  let SF := fresh "STf" in
  pose proof (stk_merge rsegs _ lo (bv_unsigned sp - 240) (bv_unsigned sp) S0 STa ltac:(lia)) as SF;
  apply evt_done; do 15 eexists; split;
  [ f_equal; rewrite BC; fin_regs
  | split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [exact SF|];
    unfold build_out; rewrite BC; exact R ].

Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma len_split_eq : forall n c, (30 + n + (30 - n) <= c)%nat ->
  (30 + n + (30 - n) + (c - (30 + n + (30 - n))))%nat = c.
Proof. intros n c H. lia. Qed.

Lemma size_cb1 : forall n (l : list byte), Z.of_nat (cells_size [CB n l]) = Z.of_nat n.
Proof. intros n l. cbn [cells_size csize]. rewrite Nat.add_0_r. reflexivity. Qed.

(* The return with the frame length at 0x184e4: the frame and the stack under it come back from
   under keep, then the buffer, the stack and the registers. Q4 and Q5 hold the body and the
   padding; Hb4, Hpad say their bytes, Hsv the sum; FLr, LEN, FLN the frame length. *)
Ltac ok_fin sp lo fl out oj bb FR STa ST0 MUO WMO MU WM Dosp Q1 Q2 P3 Q4 Q5 P6 BC Hb4 Hpad Hsv FLr LEN FLN :=
  let FRx := fresh "FRx" in let STx := fresh "STx" in
  xport FR FRx MUO WMO ltac:(unfold keep in Dosp);
  xport STa STx MUO WMO ltac:(unfold keep in Dosp);
  do 14 step;
  release_frame FRx STx (bv_unsigned sp);
  apply evt_done; do 15 eexists; split;
  [ f_equal; rewrite BC; rewrite (unsigned_lit fl) by (clear - FLr; lia); rewrite Z.add_0_r;
    rewrite swrap32_small by (clear - FLr; lia); unfold mkR; reflexivity
  | split; [exact MU|]; split; [exact WM|]; split; [assumption|];
    let OUT := fresh "OUT" in
    lazymatch goal with |- _ /\ ?G => assert (OUT : G) end;
    [ unfold build_out; rewrite BC; cbv zeta;
      let HF := fresh "HF" in
      destruct (Z.leb_spec 0 fl) as [_|HF]; [cbv iota | exfalso; clear - FLr HF; lia];
      eapply out_final; [exact Q1 | exact Q2 | exact P3 | reflexivity | exact Q4 | exact Q5 | exact P6 |
                         | apply len_split_eq; exact LEN];
      match goal with |- context [cells_bytes ?cs] =>
        let l := eval cbn [cells_bytes cbytes app] in (cells_bytes cs) in change (cells_bytes cs) with l end;
      rewrite hdr_bytes by assumption;
      rewrite <- FLN;
      apply frame_bytes_eq; [exact Hsv | exact Hb4 | exact Hpad]
    | ];
    unfold keep in ST0;
    let STl := fresh "STl" in let STf := fresh "STf" in
    pose proof (stk_rebuild _ _ lo (bv_unsigned sp - 240) (bv_unsigned sp - 240) (bv_unsigned sp) out
                  (Z.of_nat (length oj)) _ ST0 MU WM (Z.le_refl _) OUT (size_cb1 _ _)) as STl;
    pose proof (stk_merge rsegs _ lo (bv_unsigned sp - 240) (bv_unsigned sp) STl STx ltac:(assumption)) as STf;
    split; [exact STf | exact OUT] ].

Lemma sub30_0 : forall n, 29 < Z.of_nat n -> (30 - n)%nat = 0%nat.
Proof. intros n H. lia. Qed.

(* 0x184c8 .. 0x184e0 for a body under 30 bytes: the check of out + body_len + 30, then
   memset (out + body_len + 30, 0, 30 - body_len) over P5; Q5 names the zeros. *)
Ltac memset_tail MSET P5 out bb Q5 :=
  do 2 step;
  take_by false ltac:(unfold_cond; usub; rewrite zb_lxor_ones by lia; usub; fold_lit_ux; solve_cond_rec);
  do 5 step;
  let UA0 := fresh "UA0" in let UA2 := fresh "UA2" in
  assert (UA0 : bv_unsigned (Z_to_bv 64 (out + (Z.of_nat (length bb) + 30))) = out + 30 + Z.of_nat (length bb))
    by (rewrite unsigned_lit by lia; lia);
  assert (UA2 : bv_unsigned (Z_to_bv 64 (30 - bv_unsigned (Z_to_bv 64 (Z.of_nat (length bb)))))
                = Z.of_nat (30 - length bb))
    by (rewrite (unsigned_lit (Z.of_nat (length bb))) by lia; rewrite unsigned_lit by lia; lia);
  call MSET; [ rewrite UA0, UA2, Nat2Z.id; exact P5 | assumption | ];
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) [CB _ (repeat ?x _)] |- _ =>
    rewrite UA0, UA2, Nat2Z.id in H;
    replace x with (b8 0) in H by (apply bv_eq; vm_compute; reflexivity); rename H into Q5 end.

Theorem diginet_frame_build_holds :
  diginet_body_check_contract -> memcpy_contract -> diginet_sum16_contract -> memset_contract ->
  diginet_frame_build_contract.
Proof.
  intros DBC MCPY SUM MSET. unfold diginet_frame_build_contract, DIGINET_FRAME_BUILD.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
    HO Hdst Hsrc Hhp Hbody Hmode HA4 Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
    Ddst Dsrc Dhp Dbody SP8 ST LO0 LO Dosp Ddsp Dssp Dhsp Dbsp MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  pose proof (bytes_at_bound _ _ _ _ BDM) as Rdst. rewrite Ldm in Rdst.
  pose proof (bytes_at_bound _ _ _ _ BSM) as Rsrc. rewrite Lsm in Rsrc.
  pose proof (bytes_at_bound _ _ _ _ BB) as Rbb.
  pose proof (rw_cells_bound _ _ _ _ RWO) as Roj. cbn [cells_size csize] in Roj. rewrite Nat.add_0_r in Roj.
  pose proof ST as (Rlo & Rhi & _).
  assert (Rmode : 0 <= mode <= 1) by (destruct Hmode; lia).
  pose proof (hdr_ro m hp send ack retry cmd ncmds Hsend Hack Hretry BHP) as HC. clear BHP.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 240) (bv_unsigned sp) ST ltac:(lia)) as [ST0 STa].
  clear ST.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)] m) as MUS.
  pose proof (wmono_refl rsegs m) as WMS.
  hide Ddst. hide Dsrc. hide Dhp. hide Dbody. hide Dosp. hide Ddsp. hide Dssp. hide Dhsp. hide Dbsp. hide Hmode.
  hide BDM. hide BSM. hide BB. hide RWO. hide HC. hide ST0.
  carve_frame 96%nat STa.
  do 13 step.
  (* 0x18294 .. 0x182ac: out, dst, src, hp are not 0 *)
  step. take false.
  step. step. take false.
  step. step. take false.
  step. step. take false.
  (* 0x182b0 .. 0x182cc: body_len && !body *)
  do 8 step.
  take_by false ltac:(apply and_test_false; lia).
  (* 0x182d0 .. 0x182d8: mode > DIGINET_SUM_ZERO *)
  do 3 step. take false.
  (* 0x182dc: body_len > DIGINET_MAX_BODY_LEN *)
  do 2 step.
  destruct (Z_lt_le_dec 1484 (Z.of_nat (length bb))) as [BIG|SMALL].
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -4)
      by (unfold build_code; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [reflexivity | lia]).
    err_fin FR STa ST0 sp lo BC RWO MUS WMS Dosp. }
  take true.
  (* 0x182ec: diginet_body_check (body, body_len) *)
  do 3 step.
  xport BB BB1 MUS WMS ltac:(unfold keep in Dbsp).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  call DBC.
  { exact Hbody. }
  { exact BB1. }
  { rewrite USP. lia. }
  { rewrite USP. exact STa. }
  { lia. }
  { rewrite USP. lia. }
  { rewrite USP. unfold keep in Dbsp. lia. }
  { assumption. }
  lazymatch goal with H : stk _ _ _ (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite USP in H; rename H into STa end.
  (* 0x182f8: the code of diginet_body_check *)
  rewrite body_check_spec. destruct (system_at bb) eqn:SA; cbv iota; step.
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -10)
      by (unfold build_code; rewrite SA; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia | reflexivity]).
    err_fin FR STa ST0 sp lo BC RWO MUS WMS Dosp. }
  take true.
  (* 0x18304 .. 0x18314: the frame length *)
  destruct (ex_intro (fun z => z = frame_len (length bb)) _ eq_refl) as [fl EFL].
  assert (FLv : fl = Z.max 60 (30 + Z.of_nat (length bb))) by (rewrite EFL; reflexivity).
  do 3 step.
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mc ?ro) =>
      let p := eval vm_compute in (bv_key (Z_to_bv 5 24)) in
      let R' := eval cbv beta iota delta [tset] in (tset p (Z_to_bv 64 fl) R) in
      assert (K1 : evt segs Q (MS R' F (Z_to_bv 64 0x18318) fc rv mc ro))
  end.
  2: { step. destruct (Z_lt_le_dec (Z.of_nat (length bb)) 30) as [N30|N30].
       - take false. step. set_reg_tac 24 (Z_to_bv 64 fl); [f_equal; lia | exact K1].
       - take true. set_reg_tac 24 (Z_to_bv 64 fl); [f_equal; lia | exact K1]. }
  (* 0x18318: cap < frame length *)
  step.
  destruct (Z_lt_le_dec (Z.of_nat (length oj)) fl) as [CAPS|CAPOK].
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -5)
      by (unfold build_code; rewrite SA; rewrite <- EFL;
          destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|];
          destruct (Z.ltb_spec (Z.of_nat (length oj)) fl); [reflexivity | lia]).
    err_fin FR STa ST0 sp lo BC RWO MUS WMS Dosp. }
  take true.
  assert (FLr : 60 <= fl <= 1514) by lia.
  assert (LEN : (30 + length bb + (30 - length bb) <= length oj)%nat) by lia.
  assert (FLN : Z.to_nat fl = (30 + length bb + (30 - length bb))%nat) by lia.
  assert (RN : 0 <= Z.of_nat (length bb) <= 1484) by lia.
  assert (STr : lo <= bv_unsigned sp - 240 <= bv_unsigned sp) by lia.
  (* 0x18324: the writes into the buffer. The facts the writes keep move from the entry memory
     here; the frame and the stack under it go under keep, and the fence MUO starts. *)
  xport RWO RWO1 MUS WMS ltac:(unfold keep in Dosp).
  xport BDM BDM1 MUS WMS ltac:(unfold keep in Ddsp).
  xport BSM BSM1 MUS WMS ltac:(unfold keep in Dssp).
  xport HC HC1 MUS WMS ltac:(unfold keep in Dhsp).
  xport BB BB2 MUS WMS ltac:(unfold keep in Dbsp).
  clear MUS WMS BDM BSM HC BB RWO Ddsp Dssp Dhsp Dbsp.
  hide BDM1. hide BSM1. hide HC1. hide BB2. hide STa. hide FR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (munch_refl [(out, out + Z.of_nat (length oj))] mc) as MUO;
    pose proof (wmono_refl rsegs mc) as WMO end.
  destruct (out_split _ out (length bb) (30 - length bb) oj LEN RWO1)
    as ((j1 & P1) & (j2 & P2) & (j3 & P3) & (j4 & P4) & (j5 & P5) & P6).
  clear RWO1.
  assert (UO : bv_unsigned (Z_to_bv 64 out) = out) by (apply unsigned_lit; lia).
  assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  (* 0x18324: memcpy (out, dst, 6) *)
  do 4 step.
  xport BDM1 BDM2 MUO WMO ltac:(unfold keep in Ddst).
  assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
  call MCPY; [ rewrite UD; exact BDM2 | rewrite Ldm; reflexivity | rewrite UO; exact P1
             | rewrite UD, UO, U6; unfold keep in Ddst; lia | assumption | ].
  lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
    rewrite UO, U6 in H; change (Z.to_nat 6) with 6%nat in H; rename H into Q1 end.
  (* 0x18334: out + 6 wraps *)
  do 2 step. take false.
  (* 0x1833c: memcpy (out + 6, src, 6) *)
  do 4 step.
  xport BSM1 BSM2 MUO WMO ltac:(unfold keep in Dsrc).
  assert (UO6 : bv_unsigned (Z_to_bv 64 (out + 6)) = out + 6) by (apply unsigned_lit; lia).
  assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
  call MCPY; [ rewrite US; exact BSM2 | rewrite Lsm; reflexivity | rewrite UO6; exact P2
             | rewrite US, UO6, U6; unfold keep in Dsrc; lia | assumption | ].
  lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
    rewrite UO6, U6 in H; change (Z.to_nat 6) with 6%nat in H; rename H into Q2 end.
  clear BDM1 BSM1 Ddst Dsrc.
  (* 0x1834c .. 0x1839c: EtherType and numbytes, with the checks of out + 12 .. out + 16 *)
  do 2 step. take false.
  do 5 step. take false.
  do 4 step. take false.
  do 6 step. take false.
  do 3 step. take false.
  step.
  (* 0x183a0: the sum in the mode DIGINET_SUM_BODY, zero in DIGINET_SUM_ZERO; both reach
     0x183c0 with a0 the sum and a1 its high byte *)
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mc ?ro) =>
      let k1 := eval vm_compute in (bv_key (Z_to_bv 5 1)) in
      let k10 := eval vm_compute in (bv_key (Z_to_bv 5 10)) in
      let k11 := eval vm_compute in (bv_key (Z_to_bv 5 11)) in
      let k12 := eval vm_compute in (bv_key (Z_to_bv 5 12)) in
      let k13 := eval vm_compute in (bv_key (Z_to_bv 5 13)) in
      let k14 := eval vm_compute in (bv_key (Z_to_bv 5 14)) in
      let k15 := eval vm_compute in (bv_key (Z_to_bv 5 15)) in
      let k16 := eval vm_compute in (bv_key (Z_to_bv 5 16)) in
      let Rf := eval cbv beta iota delta [tset] in
        (fun (vra v1 v2 v3 v4 v5 v6 : word) (sv : Z) =>
           tset k1 vra (tset k10 (Z_to_bv 64 sv) (tset k11 v1 (tset k12 v2 (tset k13 v3
             (tset k14 v4 (tset k15 v5 (tset k16 v6 R)))))))) in
      assert (K2 : forall (vra v1 v2 v3 v4 v5 v6 : word) (sv : Z),
                sv = (if mode =? 0 then lib_sum16 bb else 0) -> v1 = Z_to_bv 64 (Z.shiftr sv 8) ->
                evt segs Q (MS (Rf vra v1 v2 v3 v4 v5 v6 sv) F (Z_to_bv 64 0x183c0) fc rv mc ro))
  end.
  2: { step. pose proof Hmode as HM. unfold keep in HM. destruct HM as [M|M]; subst mode.
       - (* 0x183b0: diginet_sum16 (body, body_len) *)
         take true. do 3 step.
         xport BB2 BB3 MUO WMO ltac:(unfold keep in Dbody).
         eapply evt_cut; [eapply SUM; [exact Hbody | exact BB3] |].
         intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & ->).
         replace (ret_pc (Z_to_bv 64 0x183bc)) with (Z_to_bv 64 0x183bc)
           by (symmetry; apply ret_pc_even; [lia | reflexivity]).
         step.
         eapply K2; [reflexivity |].
         rewrite (unsigned_lit (lib_sum16 bb)) by (rewrite lib_sum16_eq; pose proof (sum16_range bb); lia).
         reflexivity.
       - take false. do 3 step. eapply K2; reflexivity. }
  intros vra v1 v2 v3 v4 v5 v6 sv Esv Ev1. subst v1. cbv beta.
  assert (Rsv : 0 <= sv < 2^16)
    by (rewrite Esv; destruct (mode =? 0); [rewrite lib_sum16_eq; apply sum16_range | lia]).
  (* 0x183c0 .. 0x183d4: the sum, with the checks of out + 16 and out + 17 *)
  do 3 step. take false.
  do 3 step. take false.
  (* 0x183d8: the alignment of the header *)
  do 2 step.
  take_by false ltac:(unfold_cond; usub; rewrite land3_mod4 by lia; usub; fold_lit_ux; solve_cond_rec).
  (* 0x183e0 .. 0x18420: send_counter *)
  xport HC1 HC2 MUO WMO ltac:(unfold keep in Dhp).
  do 6 step. take false.
  do 4 step. take false.
  do 4 step. take false.
  do 3 step. take false.
  (* 0x18424 .. 0x18464: ack_counter *)
  xport HC1 HC3 MUO WMO ltac:(unfold keep in Dhp).
  do 6 step. take false.
  do 4 step. take false.
  do 4 step. take false.
  do 3 step. take false.
  (* 0x18468 .. 0x18488: retry *)
  xport HC1 HC4 MUO WMO ltac:(unfold keep in Dhp).
  do 6 step. take false.
  do 3 step. take false.
  (* 0x1848c .. 0x184a0: cmd and num_commands *)
  xport HC1 HC5 MUO WMO ltac:(unfold keep in Dhp).
  do 4 step. take false.
  xport HC1 HC6 MUO WMO ltac:(unfold keep in Dhp).
  do 2 step.
  clear HC1 Dhp.
  assert (BC : build_code bb (Z.of_nat (length oj)) = fl)
    by (unfold build_code; rewrite SA; rewrite <- EFL;
        destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|];
        destruct (Z.ltb_spec (Z.of_nat (length oj)) fl); [lia | reflexivity]).
  assert (Hsvz : sv = (if mode =? 1 then 0 else spec_sum bb))
    by (pose proof Hmode as HM; unfold keep in HM;
        destruct HM as [-> | ->]; rewrite Esv; cbn [Z.eqb];
        [rewrite lib_sum16_eq, spec_sum_eq; reflexivity | reflexivity]).
  (* 0x184a4: body_len is 0 *)
  step.
  destruct (Nat.eq_dec (length bb) 0) as [N0|N0].
  { take true.
    assert (Hb4 : j4 = bb).
    { pose proof P4 as [[[Lj4 _] _] _]. apply nil_of_len; [exact Lj4 | exact N0]. }
    assert (Hpad : repeat (b8 0) (30 - length bb) = repeat (b8 0) (30 - length bb)) by reflexivity.
    memset_tail MSET P5 out bb Q5.
    ok_fin sp lo fl out oj bb FR STa ST0 MUO WMO MU WM Dosp Q1 Q2 P3 P4 Q5 P6 BC Hb4 Hpad Hsvz FLr LEN FLN. }
  take false.
  (* 0x184a8: out + 30 wraps *)
  do 2 step. take false.
  (* 0x184b0: memcpy (out + 30, body, body_len) *)
  do 4 step.
  xport BB2 BB4 MUO WMO ltac:(unfold keep in Dbody).
  assert (UO30 : bv_unsigned (Z_to_bv 64 (out + 30)) = out + 30) by (apply unsigned_lit; lia).
  assert (UB : bv_unsigned (Z_to_bv 64 body) = body) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length bb))) = Z.of_nat (length bb))
    by (apply unsigned_lit; lia).
  call MCPY; [ rewrite UB; exact BB4 | rewrite UN, Nat2Z.id; reflexivity
             | rewrite UO30, UN, Nat2Z.id; exact P4
             | rewrite UB, UO30, UN; unfold keep in Dbody; lia | assumption | ].
  lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
    rewrite UO30, UN, Nat2Z.id in H; rename H into Q4 end.
  (* 0x184c0: body_len > 29 *)
  do 2 step.
  destruct (Z_lt_le_dec 29 (Z.of_nat (length bb))) as [NB|NB].
  2: { take false.
       assert (Hb4 : bb = bb) by reflexivity.
       assert (Hpad : repeat (b8 0) (30 - length bb) = repeat (b8 0) (30 - length bb)) by reflexivity.
       memset_tail MSET P5 out bb Q5.
       ok_fin sp lo fl out oj bb FR STa ST0 MUO WMO MU WM Dosp Q1 Q2 P3 Q4 Q5 P6 BC Hb4 Hpad Hsvz FLr LEN FLN. }
  take true.
  assert (Hb4 : bb = bb) by reflexivity.
  assert (Hpad : j5 = repeat (b8 0) (30 - length bb)).
  { pose proof P5 as [[[Lj5 _] _] _].
    apply nil_of_len; rewrite repeat_length; [exact Lj5 | apply sub30_0; exact NB]. }
  ok_fin sp lo fl out oj bb FR STa ST0 MUO WMO MU WM Dosp Q1 Q2 P3 Q4 P5 P6 BC Hb4 Hpad Hsvz FLr LEN FLN.
Qed.
