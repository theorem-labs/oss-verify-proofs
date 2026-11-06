From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import AsanKA AsanKAProof ReacDecodeLib check_braid_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- byte-read helpers (as in the plain proof) ---- *)
Lemma rd1 : forall m a b, mrd rsegs m (wa a) = Some b -> ov_read_bytes rsegs m (wa a) 1 = Some [b].
Proof. intros m a b H. rewrite ov_rdn, rdn_unfold, H. reflexivity. Qed.

Lemma rdw : forall m (w : word) k a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w + k = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned w + k)) 1 = Some [b].
Proof. intros m w k a b H E. rewrite E. apply rd1. exact H. Qed.

Lemma rdw0 : forall m (w : word) a b, mrd rsegs m (wa a) = Some b -> bv_unsigned w = a ->
  ov_read_bytes rsegs m w 1 = Some [b].
Proof. intros m w a b H E. rewrite <- (Z_to_bv_bv_unsigned w), E. apply rd1. exact H. Qed.

(* ---- land lemmas for the s0/s1 setup (as in the plain proof) ---- *)
Lemma land_hi : forall x k, 0 <= x < 2^64 -> 0 <= k <= 64 -> Z.land x (2^64 - 2^k) = 2^k * (x / 2^k).
Proof.
  intros x k Hx Hk.
  assert (E : 2^64 - 2^k = Z.shiftl (Z.ones (64 - k)) k).
  { rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.ones_equiv. unfold Z.pred.
    rewrite Z.mul_add_distr_r, <- Z.pow_add_r by lia. replace (64 - k + k) with 64 by lia. lia. }
  rewrite E, (Z.mul_comm (2^k)), <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, !Z.shiftl_spec by lia.
  destruct (Z.ltb_spec i k).
  - rewrite (Z.testbit_neg_r (Z.ones (64 - k)) (i - k)), (Z.testbit_neg_r (Z.shiftr x k) (i - k)) by lia.
    apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - k + k) with i by lia.
    destruct (Z.ltb_spec i 64).
    + rewrite Z.ones_spec_low by lia. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
      destruct (Z.eq_dec x 0) as [->|Hnz]; [symmetry; apply Z.bits_0|].
      symmetry. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma land_m2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551614 = 2 * (x / 2).
Proof. intros x Hx. exact (land_hi x 1 Hx ltac:(lia)). Qed.
Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof. intros x Hx. exact (land_hi x 3 Hx ltac:(lia)). Qed.
Lemma land_1u : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (Z.land_ones x 1 ltac:(lia)). Qed.

(* ---- the pair base 2*(ch/2) of a channel ch < nch: for even nch the last pair
   starts at nch - 2; for odd nch the unpaired last channel starts at nch - 1 ---- *)
Lemma pair_base_le : forall ch nch, 0 <= ch < nch -> 2 * (ch / 2) + 2 <= nch + nch mod 2.
Proof. intros ch nch H. Z.div_mod_to_equations. lia. Qed.

(* ---- transport across the frame carve ---- *)
Lemma braid_transport : forall m m' audio pcm nch ns lo hi,
  1 <= nch <= 127 -> 1 <= ns <= 127 -> 0 <= audio < 2^63 -> 0 <= pcm < 2^63 ->
  munch [(lo, hi)] m m' ->
  audio + 3 * nch * ns + 3 * (nch mod 2) <= lo \/ hi <= audio ->
  pcm + 3 * nch * ns <= lo \/ hi <= pcm ->
  braid_map m audio pcm nch ns -> braid_map m' audio pcm nch ns.
Proof.
  intros m m' audio pcm nch ns lo hi HN HS HA HP MU DA DP BR ch s j Hch Hs Hj.
  destruct (BR ch s j Hch Hs Hj) as (b & H1 & H2). exists b.
  (* nia multiplies every hypothesis pair and case-splits the disjunctions DA DP: give it only the bounds *)
  assert (NN : nch * ns <= 16129) by (clear - HN HS; nia).
  assert (I1 : 0 <= ch * ns + s <= nch * ns - 1) by (clear - HN HS Hch Hs; nia).
  assert (I2 : 0 <= s * nch + 2 * (ch / 2) <= nch * ns - 1).
  { clear - HN HS Hch Hs. pose proof (Z.mul_div_le ch 2 ltac:(lia)). pose proof (Z.div_pos ch 2 ltac:(lia) ltac:(lia)). nia. }
  assert (I3 : s * nch + 2 * (ch / 2) + 2 <= nch * ns + nch mod 2).
  { clear - HN HS Hch Hs. pose proof (pair_base_le ch nch Hch). assert (nch * s + nch <= nch * ns) by nia. nia. }
  assert (O : 0 <= braid_off ch j <= 5)
    by (unfold braid_off; destruct (Z.even ch); destruct (j =? 0); destruct (j =? 1); lia).
  unfold mrd in *. rewrite !MU; [split; assumption | | ].
  all: rewrite wa_unsigned by lia; cbn [outside]; split; [lia | exact I].
Qed.

Lemma win96_out : forall s a, 0 <= s - 96 -> app_mem (s - 96) -> app_mem (s - 1) -> app_mem a ->
  outside [(s - 96, s)] (a / 8 + ASAN_K).
Proof.
  intros s a H0 H1 H2 Ha. cbn [outside]. split; [|exact I]. intros W.
  apply (shadow_not_app a Ha). apply (app_win s 96); [lia | exact H1 | exact H2 | lia].
Qed.

Lemma addr_transport : forall m m' s p n, addressable m p n -> munch [(s - 96, s)] m m' -> 0 <= s - 96 ->
  app_mem (s - 96) -> app_mem (s - 1) -> addressable m' p n.
Proof.
  intros m m' s p n A MU H0 H1 H2. eapply addr_munch; [exact A | exact MU |].
  intros i Hi. destruct (addr_one m p n i A Hi) as (Ha & _). apply win96_out; assumption.
Qed.

(* =========================================================================
   Shadow-check lemmas (one load of the shadow byte + compare, error path
   never taken because the byte is addressable; some also fold in the data
   load that the source interleaves).  Modelled on reac_decode.v rc_c*.
   ========================================================================= *)

(* SC1 @80eec -> 80efc : addr in x14, shadow/lb into x15, handler andi x16 *)
Lemma sc1 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x14 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y15 y16 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 y15 y16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80efc) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80eec) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x14) as RS. unfold ASAN_K in M.
  step. gen_shr x14 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* SC5 @80fc0 -> 80fd0 : addr in x14, shadow/lb into x16, handler andi x23 *)
Lemma sc5 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x14 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y16 y23 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 y16 x17 x18 x19 x20 x21 x22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80fd0) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80fc0) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x14) as RS. unfold ASAN_K in M.
  step. gen_shr x14 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* E1 @80f10 -> 80f24 : addr = x15+3 (addi x16), shadow/lb into x22, handler andi x24 *)
Lemma e1 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x15 + 3 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y16 y22 y24 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 y16 x17 x18 x19 x20 x21 y22 x23 y24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f24) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f10) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x15) as RS. unfold ASAN_K in M.
  step. gen_addi x15 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* E2 @80f2c -> 80f40 : addr = x14+1 (addi x16), shadow/lb into x22, handler andi x23 *)
Lemma e2 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x14 + 1 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y16 y22 y23 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 y16 x17 x18 x19 x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f40) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f2c) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x14) as RS. unfold ASAN_K in M.
  step. gen_addi x14 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* E3 @80f40 -> 80f54 : shadow addr x15 (lb into x22), data load x16 := byte at x21, handler andi x23 *)
Lemma e3 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x15 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x21 = D -> mrd rsegs mm (wa D) = Some b ->
  (forall y22 y23 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 (zxb b) x17 x18 x19 x20 x21 y22 y23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f54) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f40) fc None mm (seg_rom rsegs)).
Proof.
  intros until D. intros EA RA M SK ED MD CONT.
  pose proof (u64_range x15) as RS. unfold ASAN_K in M.
  step. gen_shr x15 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x21 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* O1 @80f64 -> 80f78 : addr = x15+4 (addi x16), shadow/lb into x22, handler andi x24 *)
Lemma o1 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x15 + 4 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y16 y22 y24 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 y16 x17 x18 x19 x20 x21 y22 x23 y24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f78) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f64) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x15) as RS. unfold ASAN_K in M.
  step. gen_addi x15 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* O2 @80f84 -> 80f98 : addr = x14+1 (addi x16), shadow/lb into x23, handler andi x24 *)
Lemma o2 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k : byte) (A : Z),
  bv_unsigned x14 + 1 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  (forall y16 y23 y24 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 y16 x17 x18 x19 x20 x21 x22 y23 y24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f98) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f84) fc None mm (seg_rom rsegs)).
Proof.
  intros until A. intros EA RA M SK CONT.
  pose proof (u64_range x14) as RS. unfold ASAN_K in M.
  step. gen_addi x14 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* O3 @80f98 -> 80fb0 : addr = x15+5 (addi x16), shadow/lb into x24, data load x23 := byte at x21, handler andi x25 *)
Lemma o3 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x15 + 5 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x21 = D -> mrd rsegs mm (wa D) = Some b ->
  (forall y16 y24 y25 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 y16 x17 x18 x19 x20 x21 x22 (zxb b) y24 y25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80fb0) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80f98) fc None mm (seg_rom rsegs)).
Proof.
  intros until D. intros EA RA M SK ED MD CONT.
  pose proof (u64_range x15) as RS. unfold ASAN_K in M.
  step. gen_addi x15 w U. rewrite EA in U.
  step. gen_shr w g G. rewrite U in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw0 mm x21 _ _ MD ED) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, U, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* SC6 @80fd4 -> 80fe8 : shadow addr x15 (lb into x16), data load x14 := byte at x21+1, handler andi x21 *)
Lemma sc6 : forall (x1 x2 x3 x4 x5 x6 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
  (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (Q : machine_state -> Prop) (k b : byte) (A D : Z),
  bv_unsigned x15 = A -> A < 2^64 ->
  mrd rsegs mm (wa (A / 8 + ASAN_K)) = Some k ->
  (bv_signed k = 0 \/ A mod 8 < bv_signed k) ->
  bv_unsigned x21 = D -> mrd rsegs mm (wa (D + 1)) = Some b ->
  (forall y16 y21 : word,
     evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 (zxb b) x15 y16 x17 x18 x19 x20 y21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80fe8) fc None mm (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR x1 x2 x3 x4 x5 x6 (Z_to_bv 64 2147450880) x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x80fd4) fc None mm (seg_rom rsegs)).
Proof.
  intros until D. intros EA RA M SK ED MD CONT.
  pose proof (u64_range x15) as RS. pose proof (u64_range x21) as R21. unfold ASAN_K in M.
  step. gen_shr x15 g G. rewrite EA in G.
  step. gen_addi g h H.
  pose proof (rdw0 mm h _ _ M ltac:(lia)) as R. step. clear R.
  pose proof (rdw mm x21 1 _ _ MD ltac:(lia)) as R. step. clear R.
  step.
  pose proof (Z.mod_pos_bound A 8 ltac:(lia)) as MB.
  destruct SK as [C|C].
  - rewrite sxb_eq0, (proj2 (Z.eqb_eq _ _) C); cbn [negb]. apply CONT.
  - rewrite sxb_eq0, (proj2 (Z.eqb_neq (bv_signed k) 0) ltac:(lia)); cbn [negb].
    step. step. rewrite land7, EA, (lts_low (A mod 8) k MB), (proj2 (Z.ltb_lt _ _) C); cbn [negb].
    step. apply CONT.
Qed.

(* =========================================================================
   Loops
   ========================================================================= *)

Ltac rng := lia.
Ltac wsub := repeat match goal with H : bv_unsigned ?w = _ |- context [bv_unsigned ?w] => is_var w; rewrite H end.
Ltac usub := repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by rng end.
Ltac shn := rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; zb_fold_lits.
Ltac lnd := repeat match goal with
  | |- context [Z.land ?x 18446744073709551614] => rewrite (land_m2 x) by rng
  | |- context [Z.land ?x 18446744073709551608] => rewrite (land_m8 x) by rng
  | |- context [Z.land ?x 1] => rewrite (land_1u x)
  end.
Ltac norm := wsub; do 3 (shn; usub; lnd).
Ltac fact := rewrite ?v_sltu_b2z, ?Z.lxor_nilpotent; norm; first [ reflexivity | rng | (vm_compute; reflexivity) ].
Ltac solve_c := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?zb_signed; norm;
  do 3 (decide_tests; cbv beta iota); reflexivity.
Ltac take b := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_c]
  end.

Section Loops.
Variables (ra sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (audio pcm nch ns : Z) (t1 t3 t4 : word).
Hypothesis HN : 1 <= nch <= 127.
Hypothesis HS : 1 <= ns <= 127.
Hypothesis HA : 0 <= audio < 2^63.
Hypothesis HP : 0 <= pcm < 2^63.
Hypothesis BR : braid_map m audio pcm nch ns.
Hypothesis AAD : addressable m audio (3 * nch * ns + 3 * (nch mod 2)).
Hypothesis APD : addressable m pcm (3 * nch * ns).
Hypothesis Ht1 : bv_unsigned t1 = 3 * ns.
Hypothesis Ht3 : bv_unsigned t3 = 3 * ns.
Hypothesis Ht4 : bv_unsigned t4 = 3 * nch.
Variable Q : machine_state -> Prop.

Local Notation ST pc t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6 :=
  (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 2147450880) s0 s1 (Z_to_bv 64 audio) a1 (Z_to_bv 64 nch) (Z_to_bv 64 ns)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

Lemma body : forall ch s (t0 a1 t5 s0 s1 a7 t6 s2 s3 a4 a5 a6 s4 s5 s6 s7 s8 s9 : word),
  0 <= ch < nch -> 0 <= s < ns ->
  bv_unsigned a7 = 0 ->
  bv_unsigned t0 = ch ->
  bv_unsigned a1 = pcm + 3 * ns * ch ->
  bv_unsigned t5 = pcm + 1 + 3 * ns * ch ->
  bv_unsigned s0 = 3 * (2 * (ch / 2)) ->
  bv_unsigned s1 = ch mod 2 ->
  bv_unsigned t6 = 3 * s ->
  bv_unsigned s2 = audio + 3 * nch * s ->
  bv_unsigned s3 = audio + 3 * nch * s ->
  (forall (a4' a5' a6' a7' s4' s5' s6' s7' s8' s9' s2' s3' t6' : word),
     bv_unsigned a7' = 0 ->
     bv_unsigned t6' = 3 * (s + 1) ->
     bv_unsigned s2' = audio + 3 * nch * (s + 1) ->
     bv_unsigned s3' = audio + 3 * nch * (s + 1) ->
     evt rsegs Q (ST 0x81010 t0 s0 s1 a1 a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' t5 t6')) ->
  evt rsegs Q (ST 0x80ee8 t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6).
Proof.
  intros ch s t0 a1 t5 s0 s1 a7 t6 s2 s3 a4 a5 a6 s4 s5 s6 s7 s8 s9
    Hch Hs Ha7 Ht0 Ha1 Ht5 Hs0 Hs1 Ht6 Hs2 Hs3 K.
  assert (B1 : 0 <= ns * ch <= 16129) by nia.
  assert (B2 : 0 <= nch * s <= 16129) by nia.
  assert (Bnn : 3 * nch * ns <= 48387) by nia.
  assert (Hd1 : 0 <= ch / 2) by (apply Z.div_pos; lia).
  assert (Hd2 : 2 * (ch / 2) <= ch) by (pose proof (Z.mul_div_le ch 2 ltac:(lia)); lia).
  assert (Hm2 : 0 <= nch mod 2 < 2) by (apply Z.mod_pos_bound; lia).
  assert (Hpb : 2 * (ch / 2) + 2 <= nch + nch mod 2) by (apply pair_base_le; exact Hch).
  assert (B3 : nch * s + nch <= nch * ns) by nia.
  assert (BP0 : 0 <= 3 * ns * ch + 3 * s < 3 * nch * ns) by nia.
  assert (BP1 : 0 <= 3 * ns * ch + 3 * s + 1 < 3 * nch * ns) by nia.
  assert (BP2 : 0 <= 3 * ns * ch + 3 * s + 2 < 3 * nch * ns) by nia.
  assert (BA0 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA1 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 1 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA2 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 2 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA3 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 3 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA4 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 4 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (BA5 : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) + 5 < 3 * nch * ns + 3 * (nch mod 2)) by nia.
  assert (Bgp : 0 <= 3 * ns * ch + 3 * s < 2 ^ 31) by nia.
  assert (Bga : 0 <= 3 * nch * s + 3 * (2 * (ch / 2)) < 2 ^ 31) by nia.
  clear B1 B2 B3 Bnn Hd1 Hd2 Hpb.
  destruct (BR ch s 0 Hch Hs ltac:(lia)) as (b0 & P0 & A0).
  destruct (BR ch s 1 Hch Hs ltac:(lia)) as (b1 & P1 & A1).
  destruct (BR ch s 2 Hch Hs ltac:(lia)) as (b2 & P2 & A2).
  unfold braid_off in A0, A1, A2.
  pose proof (Zmod_even ch) as Hevm.
  (* 80ee8 add a4,a1,t6 : a4 = pcm+p *)
  step. gen_add a1 t6 wa4 Ua4.
  assert (EA4 : bv_unsigned wa4 = pcm + (3 * ns * ch + 3 * s)) by (rewrite Ua4, Ha1, Ht6; lia). clear Ua4.
  destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s) APD BP0) as (_ & kp0 & Mp0 & Sp0). clear BP0.
  eapply sc1 with (A := pcm + (3 * ns * ch + 3 * s)) (k := kp0);
    [ exact EA4 | lia | exact Mp0 | exact Sp0 | ]. clear kp0 Mp0 Sp0.
  intros a5a a6a.
  (* 80efc add s5,t5,t6 : s5 = pcm+1+p *)
  step. gen_add t5 t6 ws5 Us5.
  assert (ES5 : bv_unsigned ws5 = pcm + 1 + (3 * ns * ch + 3 * s)) by (rewrite Us5, Ht5, Ht6; lia). clear Us5.
  (* 80f00 lbu s7,-1(s5) : pcm[p] = b0 *)
  pose proof (rdw m ws5 (-1) _ _ P0 ltac:(nia)) as R. step. clear R P0.
  (* 80f04 add s4,s2,s0 : s4 = audio+g *)
  step. gen_add s2 s0 ws4 Us4.
  assert (ES4 : bv_unsigned ws4 = audio + (3 * nch * s + 3 * (2 * (ch / 2)))) by (rewrite Us4, Hs2, Hs0; lia). clear Us4.
  (* 80f08 add a5,s0,s3 : a5 = audio+g *)
  step. gen_add s0 s3 wa5 Ua5.
  assert (EA5 : bv_unsigned wa5 = audio + (3 * nch * s + 3 * (2 * (ch / 2)))) by (rewrite Ua5, Hs0, Hs3; lia). clear Ua5.
  destruct (Z.even ch) eqn:Eev.
  - (* even : ch mod 2 = 0 *)
    assert (Hc2 : ch mod 2 = 0) by (rewrite Zmod_even, Eev; reflexivity).
    rewrite Hc2 in Hs1. clear Hc2.
    cbn [Z.eqb Pos.eqb] in A0, A1, A2.
    step. take false.
    (* E1 : shadow audio+g+3 *)
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 3) AAD BA3) as (_ & ka0 & Ma0 & Sa0). clear BA3.
    eapply e1 with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 3)) (k := ka0);
      [ rewrite EA5; lia | lia | exact Ma0 | exact Sa0 | ]. clear ka0 Ma0 Sa0.
    intros a6b s6a s8a.
    (* 80f24 lbu a6,3(s4) : audio[g+3] = b0 ; 80f28 bne *)
    pose proof (rdw m ws4 3 _ _ A0 ltac:(nia)) as R. step. clear R A0.
    step. take false.
    (* E2 : shadow pcm+p+1 *)
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 1) APD BP1) as (_ & kp1 & Mp1 & Sp1). clear BP1.
    eapply e2 with (A := pcm + (3 * ns * ch + 3 * s + 1)) (k := kp1);
      [ rewrite EA4; lia | lia | exact Mp1 | exact Sp1 | ]. clear kp1 Mp1 Sp1.
    intros a6c s6b s7a.
    (* E3 : shadow audio+g, data pcm[p+1] = b1 into a6 *)
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2))) AAD BA0) as (_ & ka1 & Ma1 & Sa1). clear BA0.
    eapply e3 with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)))) (b := b1) (D := pcm + 3 * (ch * ns + s) + 1);
      [ exact EA5 | lia | exact Ma1 | exact Sa1 | rewrite ES5; nia | exact P1 | ]. clear ka1 Ma1 Sa1 P1.
    intros s6c s7b.
    (* 80f54 lbu s7,0(s4) : audio[g+0] = b1 ; 80f58 li ; 80f5c beq *)
    pose proof (rdw0 m ws4 _ _ A1 ltac:(nia)) as R. step. clear R A1.
    step. step. take true.
    (* 80fbc addi a4,a4,2 *)
    step. gen_addi wa4 wa4b Ua4b.
    assert (EA4b : bv_unsigned wa4b = pcm + (3 * ns * ch + 3 * s) + 2) by (rewrite Ua4b, EA4; lia). clear Ua4b EA4.
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 2) APD BP2) as (_ & kp2 & Mp2 & Sp2). clear BP2.
    eapply sc5 with (A := pcm + (3 * ns * ch + 3 * s + 2)) (k := kp2);
      [ rewrite EA4b; lia | lia | exact Mp2 | exact Sp2 | ]. clear kp2 Mp2 Sp2 EA4b.
    intros a6d s7c.
    (* 80fd0 add a5,a5,s6 : a5 = audio+g+1 *)
    step. gen_addi wa5 wa5b Ua5b.
    assert (EA5b : bv_unsigned wa5b = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 1) by (rewrite Ua5b, EA5; lia). clear Ua5b EA5.
    (* SC6 : shadow audio+g+1, data pcm[p+2] = b2 into a4 *)
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 1) AAD BA1) as (_ & ka2 & Ma2 & Sa2). clear BA1.
    eapply sc6 with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 1)) (b := b2) (D := pcm + 3 * (ch * ns + s) + 1);
      [ rewrite EA5b; lia | lia | exact Ma2 | exact Sa2 | rewrite ES5; nia | | ]. clear ka2 Ma2 Sa2 EA5b ES5.
    { replace (pcm + 3 * (ch * ns + s) + 1 + 1) with (pcm + 3 * (ch * ns + s) + 2) by lia. exact P2. }
    intros a6e s5a. clear P2.
    (* 80fe8 add s4,s4,s6 : s4 = audio+g+1 *)
    step. gen_addi ws4 ws4b Us4b.
    assert (ES4b : bv_unsigned ws4b = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 1) by (rewrite Us4b, ES4; lia). clear Us4b ES4.
    (* 80fec lbu a5,0(s4) : audio[g+1] = b2 *)
    pose proof (rdw0 m ws4b _ _ A2 ltac:(nia)) as R. step. clear R A2.
    do 7 step.
    apply K; fact.
  - (* odd : ch mod 2 = 1 *)
    assert (Hc2 : ch mod 2 = 1) by (rewrite Zmod_even, Eev; reflexivity).
    rewrite Hc2 in Hs1. clear Hc2.
    cbn [Z.eqb Pos.eqb] in A0, A1, A2.
    step. take true.
    (* O1 : shadow audio+g+4 *)
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 4) AAD BA4) as (_ & ka0 & Ma0 & Sa0). clear BA4.
    eapply o1 with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 4)) (k := ka0);
      [ rewrite EA5; lia | lia | exact Ma0 | exact Sa0 | ]. clear ka0 Ma0 Sa0.
    intros a6b s6a s8a.
    (* 80f78 lbu a6,4(s4) : audio[g+4] = b0 ; 80f7c li ; 80f80 bne *)
    pose proof (rdw m ws4 4 _ _ A0 ltac:(nia)) as R. step. clear R A0.
    step. step. take false.
    (* O2 : shadow pcm+p+1 *)
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 1) APD BP1) as (_ & kp1 & Mp1 & Sp1). clear BP1.
    eapply o2 with (A := pcm + (3 * ns * ch + 3 * s + 1)) (k := kp1);
      [ rewrite EA4; lia | lia | exact Mp1 | exact Sp1 | ]. clear kp1 Mp1 Sp1.
    intros a6c s7a s8b.
    (* O3 : shadow audio+g+5, data pcm[p+1] = b1 into s7 *)
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 5) AAD BA5) as (_ & ka1 & Ma1 & Sa1). clear BA5.
    eapply o3 with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 5)) (b := b1) (D := pcm + 3 * (ch * ns + s) + 1);
      [ rewrite EA5; lia | lia | exact Ma1 | exact Sa1 | rewrite ES5; nia | exact P1 | ]. clear ka1 Ma1 Sa1 P1.
    intros a6d s8c s9a.
    (* 80fb0 lbu a6,5(s4) : audio[g+5] = b1 ; 80fb4 bne ; 80fb8 li s6,2 *)
    pose proof (rdw m ws4 5 _ _ A1 ltac:(nia)) as R. step. clear R A1.
    step. take false.
    step.
    (* 80fbc addi a4,a4,2 *)
    step. gen_addi wa4 wa4b Ua4b.
    assert (EA4b : bv_unsigned wa4b = pcm + (3 * ns * ch + 3 * s) + 2) by (rewrite Ua4b, EA4; lia). clear Ua4b EA4.
    destruct (addr_one m pcm (3 * nch * ns) (3 * ns * ch + 3 * s + 2) APD BP2) as (_ & kp2 & Mp2 & Sp2). clear BP2.
    eapply sc5 with (A := pcm + (3 * ns * ch + 3 * s + 2)) (k := kp2);
      [ rewrite EA4b; lia | lia | exact Mp2 | exact Sp2 | ]. clear kp2 Mp2 Sp2 EA4b.
    intros a6e s7b.
    (* 80fd0 add a5,a5,s6 : a5 = audio+g+2 *)
    step. gen_addi wa5 wa5b Ua5b.
    assert (EA5b : bv_unsigned wa5b = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 2) by (rewrite Ua5b, EA5; lia). clear Ua5b EA5.
    (* SC6 : shadow audio+g+2, data pcm[p+2] = b2 into a4 *)
    destruct (addr_one m audio (3 * nch * ns + 3 * (nch mod 2)) (3 * nch * s + 3 * (2 * (ch / 2)) + 2) AAD BA2) as (_ & ka2 & Ma2 & Sa2). clear BA2.
    eapply sc6 with (A := audio + (3 * nch * s + 3 * (2 * (ch / 2)) + 2)) (b := b2) (D := pcm + 3 * (ch * ns + s) + 1);
      [ rewrite EA5b; lia | lia | exact Ma2 | exact Sa2 | rewrite ES5; nia | | ]. clear ka2 Ma2 Sa2 EA5b ES5.
    { replace (pcm + 3 * (ch * ns + s) + 1 + 1) with (pcm + 3 * (ch * ns + s) + 2) by lia. exact P2. }
    intros a6f s5a. clear P2.
    (* 80fe8 add s4,s4,s6 : s4 = audio+g+2 *)
    step. gen_addi ws4 ws4b Us4b.
    assert (ES4b : bv_unsigned ws4b = audio + (3 * nch * s + 3 * (2 * (ch / 2))) + 2) by (rewrite Us4b, ES4; lia). clear Us4b ES4.
    (* 80fec lbu a5,0(s4) : audio[g+2] = b2 *)
    pose proof (rdw0 m ws4b _ _ A2 ltac:(nia)) as R. step. clear R A2.
    do 7 step.
    apply K; fact.
Qed.

Lemma inner_loop : forall ch (t0 a1 t5 s0 s1 : word),
  0 <= ch < nch -> bv_unsigned t0 = ch ->
  bv_unsigned a1 = pcm + 3 * ns * ch -> bv_unsigned t5 = pcm + 1 + 3 * ns * ch ->
  bv_unsigned s0 = 3 * (2 * (ch / 2)) -> bv_unsigned s1 = ch mod 2 ->
  (forall (a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t6 : word), bv_unsigned a7 = 0 ->
     evt rsegs Q (ST 0x81084 t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6)) ->
  forall n s (a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t6 : word),
  0 <= s -> s + Z.of_nat (S n) = ns ->
  bv_unsigned a7 = 0 ->
  bv_unsigned t6 = 3 * s ->
  bv_unsigned s2 = audio + 3 * nch * s -> bv_unsigned s3 = audio + 3 * nch * s ->
  evt rsegs Q (ST 0x80ee8 t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6).
Proof.
  intros ch t0 a1 t5 s0 s1 Hch Ht0 Ha1 Ht5 Hs0 Hs1 K n.
  induction n as [|n IH]; intros s a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t6 Hsz Hsn Ha7 Ht6 Hs2 Hs3.
  - apply (body ch s t0 a1 t5 s0 s1 a7 t6 s2 s3 a4 a5 a6 s4 s5 s6 s7 s8 s9);
      try assumption; [lia|].
    intros a4' a5' a6' a7' s4' s5' s6' s7' s8' s9' s2' s3' t6' Ha7' Ht6' Hs2' Hs3'.
    step. take false. step. apply K. exact Ha7'.
  - apply (body ch s t0 a1 t5 s0 s1 a7 t6 s2 s3 a4 a5 a6 s4 s5 s6 s7 s8 s9);
      try assumption; [lia|].
    intros a4' a5' a6' a7' s4' s5' s6' s7' s8' s9' s2' s3' t6' Ha7' Ht6' Hs2' Hs3'.
    step. take true. apply (IH (s + 1)); try assumption; lia.
Qed.

Lemma outer_loop :
  (forall (t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6 : word), bv_unsigned a7 = 0 ->
     evt rsegs Q (ST 0x81094 t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6)) ->
  forall k ch (t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6 : word),
  0 <= ch -> ch + Z.of_nat (S k) = nch ->
  bv_unsigned a7 = 0 -> bv_unsigned t0 = ch ->
  bv_unsigned a1 = pcm + 3 * ns * ch -> bv_unsigned t5 = pcm + 1 + 3 * ns * ch ->
  evt rsegs Q (ST 0x80ec4 t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6).
Proof.
  intros K k. induction k as [|k IH];
    intros ch t0 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t5 t6 Hc0 Hck Ha7 Ht0 Ha1 Ht5.
  all: assert (Hch : 0 <= ch < nch) by lia.
  all: assert (B1 : 0 <= ns * ch <= 16129) by nia.
  all: assert (Hd1 : 0 <= ch / 2) by (apply Z.div_pos; lia).
  all: step; take false.
  all: do 8 step.
  all: eapply (inner_loop ch) with (n := Z.to_nat (ns - 1)) (s := 0) (t0 := t0) (a1 := a1) (t5 := t5);
    [ exact Hch | exact Ht0 | exact Ha1 | exact Ht5
    | rewrite Ht0; rewrite Z.shiftl_mul_pow2 by lia;
      rewrite (unsigned_lit (ch * 2 ^ 2)) by lia;
      rewrite (land_m8 (ch * 2 ^ 2)) by lia;
      rewrite (land_m2 ch) by lia;
      rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8))) by (Z.div_mod_to_equations; lia);
      rewrite (unsigned_lit (2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
      rewrite (unsigned_lit (8 * (ch * 2 ^ 2 / 8) - 2 * (ch / 2))) by (Z.div_mod_to_equations; lia);
      Z.div_mod_to_equations; lia
    | rewrite Ht0; rewrite (land_1u ch); rewrite (unsigned_lit (ch mod 2)) by (Z.div_mod_to_equations; lia); reflexivity
    |
    | lia
    | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
    | exact Ha7
    | rewrite (unsigned_lit 0) by lia; lia
    | rewrite (unsigned_lit audio) by lia; lia
    | rewrite (unsigned_lit audio) by lia; lia ].
  - intros a4z a5z a6z a7z s2z s3z s4z s5z s6z s7z s8z s9z t6z Ha7z.
    do 3 step. step. take false. apply K. exact Ha7z.
  - intros a4z a5z a6z a7z s2z s3z s4z s5z s6z s7z s8z s9z t6z Ha7z.
    do 3 step. step. take true.
    apply (IH (ch + 1));
      [ lia | lia | exact Ha7z
      | rewrite (unsigned_lit (bv_unsigned t0 + 1)) by lia; rewrite Ht0; lia
      | rewrite (unsigned_lit (bv_unsigned a1 + bv_unsigned t1)) by (rewrite Ha1, Ht1; nia); rewrite Ha1, Ht1; nia
      | rewrite (unsigned_lit (bv_unsigned t5 + bv_unsigned t1)) by (rewrite Ht5, Ht1; nia); rewrite Ht5, Ht1; nia ].
Qed.

End Loops.

Theorem check_braid_holds : check_braid_contract.
Proof.
  unfold check_braid_contract, CHECK_BRAID, CHECK_BRAID_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m audio pcm nch ns lo
    HN HS HA HP BR STK HLO DA DP CELLS APW1 APW2 DC AAD APD.
  pose proof (u64_range sp) as Rsp.
  pose proof (proj1 STK) as Hlo0.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 96%nat STK.
  do 12 step.
  match goal with MU' : munch _ m ?m1 |- _ =>
    assert (BR1 : braid_map m1 audio pcm nch ns)
      by exact (braid_transport m m1 audio pcm nch ns (bv_unsigned sp + -96) (bv_unsigned sp) HN HS HA HP MU' DA DP BR);
    assert (AAD1 : addressable m1 audio (3 * nch * ns + 3 * (nch mod 2)))
      by exact (addr_transport m m1 (bv_unsigned sp) audio (3 * nch * ns + 3 * (nch mod 2)) AAD MU' ltac:(lia) APW1 APW2);
    assert (APD1 : addressable m1 pcm (3 * nch * ns))
      by exact (addr_transport m m1 (bv_unsigned sp) pcm (3 * nch * ns) APD MU' ltac:(lia) APW1 APW2);
    assert (CELLS1 : asan_cells m1)
      by (eapply asan_cells_munch;
          [ exact CELLS | exact MU'
          | unfold off_stk in DC; unfold GOT_CELL_K, MIDEND in DC |- *; lia ])
  end.
  step. take false.
  pose proof CELLS1 as (CK & GCK & _).
  unfold CELL_K, GOT_CELL_K, ASAN_K in CK, GCK.
  pose proof (rd_all _ _ _ GCK) as RDG. rewrite length_le8 in RDG.
  pose proof (rd_all _ _ _ CK) as RDS. rewrite length_le8 in RDS.
  do 5 step. step. do 3 step. step. do 4 step. clear RDG RDS CK GCK.
  assert (D32 : ns * 2 ^ 32 / 2 ^ 32 = ns) by (apply Z.div_mul; lia).
  assert (D31 : ns * 2 ^ 32 / 2 ^ 31 = 2 * ns)
    by (replace (ns * 2 ^ 32) with (2 * ns * 2 ^ 31) by lia; apply Z.div_mul; lia).
  eapply outer_loop with (k := Z.to_nat (nch - 1)) (ch := 0);
    [ exact HN | exact HS | exact HA | exact HP | exact BR1 | exact AAD1 | exact APD1
    | repeat first [ rewrite (unsigned_lit ns) by lia | rewrite Z.shiftl_mul_pow2 by lia
        | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end ]; lia
    | repeat first [ rewrite (unsigned_lit ns) by lia | rewrite Z.shiftl_mul_pow2 by lia
        | rewrite Z.shiftr_div_pow2 by lia | rewrite D31 | rewrite D32
        | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
            rewrite (unsigned_lit e) by (first [ lia | Z.div_mod_to_equations; lia ]) end ]; lia
    | repeat first [ rewrite (unsigned_lit nch) by lia | rewrite Z.shiftl_mul_pow2 by lia
        | match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end ]; lia
    | intros t0e s0e s1e a1e a4e a5e a6e a7e s2e s3e s4e s5e s6e s7e s8e s9e t5e t6e Ha7e;
      step; take false; do 13 step;
      apply evt_done; do 16 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
      release_frame FR STK (bv_unsigned sp); exact STK
    | lia
    | rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia
    | rewrite (unsigned_lit 0) by lia; lia
    | rewrite (unsigned_lit 0) by lia; lia
    | rewrite ?wa_unsigned by lia;
      repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end); lia
    | rewrite ?wa_unsigned by lia;
      repeat (match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end); lia ].
Qed.
