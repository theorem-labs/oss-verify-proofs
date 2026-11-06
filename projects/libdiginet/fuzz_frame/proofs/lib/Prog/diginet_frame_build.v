(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/mbedtls/fuzz_pkcs7/lib/Lib/Asn1Aux.v; 533 of its 587 lines of code are new or changed and 395 lines of the source are left out. *)
(* Walk of diginet_frame_build (src/diginet_frame.c:93-127 at 835f336c) in fuzz_frame.plain,
   0x138ac..0x13aac, against diginet_frame_build_c.v. The exits -4, -10 and -5 restore the frame
   and leave the buffer as it was. On the frame length the walk splits the buffer into the two
   MACs, the 18 header bytes, the body, the pad and the rest (out_split); runs the memcpy of each
   MAC, the header stores (sum_loop gives the sum in mode 0), the memcpy of the body and the
   memset of the pad; and joins the parts again (join6). hdr_eq and frame_bytes_eq show that the
   bytes are build_frame. The disjointness facts, and the facts the writes do not touch, are under
   keep; they move from a fence (MUS for the frame and diginet_body_check, MUO for the buffer) to
   the current memory with xport.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac
  Bytes ZBridge.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import diginet_frame_build_c diginet_body_check_c
  memcpy_c memset_c.
Import ListNotations.
Open Scope Z_scope.

(** * Tactics *)

(* A byte the function loaded and stores again (le1 (zxb b)) is the cell C1 b; any other byte
   store of v is the cell of the low byte of v. *)
Ltac fix_lit_store ::=
  match goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (zxb ?b))) _) => rewrite (le1_zxb b)
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

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

(** * The stack below the frame *)

(* A copy of the caller's stack fact the step tactics do not move. *)
Definition stk0 (m : word -> option byte) (lo hi : Z) : Prop := stk rsegs m lo hi.

(* The stack under the 240 bytes below sp after the call: outside the footprint the bytes are
   those of the entry, inside it they are the bytes of the buffer. *)
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

(** * The bytes the stores write *)

Lemma z8_u64 : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = b8 z.
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64. change (Z.of_N 8) with 8. apply mod_mod_pow2. lia.
Qed.

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

Lemma sx16_agree : forall v, 0 <= v < 2^16 -> bv_unsigned (sx16 (Z_to_bv 64 v)) mod 2^16 = v.
Proof.
  intros v Hv. unfold sx16. rewrite (unsigned_lit v) by lia. rewrite unsigned_lit_wrap.
  rewrite mod_mod_pow2 by lia. rewrite (swrap_mod 16) by lia. apply Z.mod_small. exact Hv.
Qed.

Lemma swrap32_small : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof. intros z Hz. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Lemma swrap32_mod : forall z, bv_swrap 32 z mod 2^32 = z mod 2^32.
Proof. intros z. exact (swrap_mod 32 z ltac:(lia)). Qed.

Lemma z8_shr32 : forall v k, 0 <= v < 2^32 -> 0 <= k <= 24 ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 v))) k))) = b8 (v / 2^k).
Proof. intros v k Hv Hk. rewrite z8_u64. apply (b8_shr_agree _ _ _ 32); [apply sx32_agree; lia | lia | lia]. Qed.

Lemma z8_low32 : forall v, 0 <= v < 2^32 -> Z_to_bv 8 (bv_unsigned (sx32 (Z_to_bv 64 v))) = b8 v.
Proof.
  intros v Hv. change (b8 (bv_unsigned (sx32 (Z_to_bv 64 v))) = b8 v).
  apply (b8_agree _ _ 32); [apply sx32_agree; lia | lia].
Qed.

Lemma z8_shr16 : forall v k, 0 <= v < 2^16 -> 0 <= k <= 8 ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx16 (Z_to_bv 64 v))) k))) = b8 (v / 2^k).
Proof. intros v k Hv Hk. rewrite z8_u64. apply (b8_shr_agree _ _ _ 16); [apply sx16_agree; lia | lia | lia]. Qed.

Lemma z8_low16 : forall v, 0 <= v < 2^16 -> Z_to_bv 8 (bv_unsigned (sx16 (Z_to_bv 64 v))) = b8 v.
Proof.
  intros v Hv. change (b8 (bv_unsigned (sx16 (Z_to_bv 64 v))) = b8 v).
  apply (b8_agree _ _ 16); [apply sx16_agree; lia | lia].
Qed.

Lemma z8_len_hi : forall z, 0 <= z <= 1484 ->
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (z + 16))) 8))) = b8 ((16 + z) / 2^8).
Proof.
  intros z Hz. rewrite (unsigned_lit (z + 16)) by lia. rewrite z8_u64. rewrite Z.shiftr_div_pow2 by lia.
  f_equal. f_equal. lia.
Qed.

Lemma z8_len_lo : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (z + 16))) = b8 (16 + z).
Proof. intros z. rewrite z8_u64. f_equal. lia. Qed.

(* The two bytes of the sum after srliw a1, a0, 8 (0x139dc). *)
Lemma z8_sum_hi : forall S,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 S))) 8)))) =
  b8 ((S mod 2^16) / 2^8).
Proof.
  intros S. rewrite z8_u64.
  rewrite (b8_agree _ (Z.shiftr (bv_wrap 32 (bv_unsigned (Z_to_bv 64 S))) 8 mod 2^32) 32);
    [| apply swrap32_mod | lia].
  rewrite b8_mod_w by lia.
  rewrite unsigned_lit_wrap. unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite mod_mod_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (b8_div_mod S 8 32) by lia. rewrite (b8_div_mod S 8 16) by lia. reflexivity.
Qed.

Lemma z8_sum_lo : forall S, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 S)) = b8 (S mod 2^16).
Proof. intros S. rewrite z8_u64. symmetry. apply b8_mod_w. lia. Qed.

(** * The bytes of the frame *)

(* The 18 bytes from the EtherType to num_commands (src/diginet_frame.c:113-121). *)
Definition hdr_bytes (n : nat) (sv send ack retry cmd ncmds : Z) : list byte :=
  put16 0x885f ++ put16 (16 + Z.of_nat n) ++ put16 sv ++ put32 send ++ put32 ack ++ put16 retry ++
  [b8 cmd; b8 ncmds].

Lemma frame_bytes_eq : forall dmac smac send ack retry cmd ncmds bb mode pad rest,
  pad = repeat (b8 0) (30 - length bb) ->
  build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1) ++ rest =
  dmac ++ smac ++ hdr_bytes (length bb) (if mode =? 1 then 0 else spec_sum bb) send ack retry cmd ncmds
    ++ bb ++ pad ++ rest.
Proof. intros. subst pad. unfold build_frame, hdr_bytes. rewrite <- !app_assoc. reflexivity. Qed.

(* The cells the 18 stores 0x139a4 .. 0x13a44 leave at buf + 12; c4 and c5 are the sum. *)
Lemma hdr_eq : forall (n : nat) sv send ack retry cmd ncmds (c4 c5 : byte),
  Z.of_nat n <= 1484 -> 0 <= send < 2^32 -> 0 <= ack < 2^32 -> 0 <= retry < 2^16 ->
  c4 = b8 (sv / 2^8) -> c5 = b8 sv ->
  hdr_bytes n sv send ack retry cmd ncmds =
  cells_bytes
    [C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 136))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 95)));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.of_nat n + 16))) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.of_nat n + 16))));
     C1 c4; C1 c5;
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 send))) 24))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 send))) 16))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 send))) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (sx32 (Z_to_bv 64 send))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 ack))) 24))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 ack))) 16))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx32 (Z_to_bv 64 ack))) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (sx32 (Z_to_bv 64 ack))));
     C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_unsigned (sx16 (Z_to_bv 64 retry))) 8))));
     C1 (Z_to_bv 8 (bv_unsigned (sx16 (Z_to_bv 64 retry))));
     C1 (b8 cmd); C1 (b8 ncmds)].
Proof.
  intros n sv send ack retry cmd ncmds c4 c5 Hn Hs Ha Hr -> ->.
  unfold hdr_bytes, put16, put32. cbn [cells_bytes cbytes app].
  rewrite (z8_len_hi (Z.of_nat n)) by lia. rewrite z8_len_lo.
  rewrite !z8_shr32 by lia. rewrite !z8_low32 by lia. rewrite z8_shr16 by lia. rewrite z8_low16 by lia.
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 136))) with (b8 (34911 / 2^8)) by (apply bv_eq; vm_compute; reflexivity).
  replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 95))) with (b8 34911) by (apply bv_eq; vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma cb1_bytes : forall k l, cells_bytes [CB k l] = l.
Proof. intros k l. cbn [cells_bytes cbytes]. apply app_nil_r. Qed.

(* The buffer after the writes, from its six parts. *)
Lemma join6 : forall m A (n pad r : nat) a b hdr c d e,
  rw_cells rsegs m A [CB 6 a] -> rw_cells rsegs m (A + 6) [CB 6 b] ->
  rw_cells rsegs m (A + 12) hdr -> cells_size hdr = 18%nat ->
  rw_cells rsegs m (A + 30) [CB n c] -> rw_cells rsegs m (A + (Z.of_nat n + 30)) [CB pad d] ->
  rw_cells rsegs m (A + (Z.of_nat n + 30) + Z.of_nat pad) [CB r e] ->
  rw_cells rsegs m A [CB (30 + n + pad + r) (a ++ b ++ cells_bytes hdr ++ c ++ d ++ e)].
Proof.
  intros m A n pad r a b hdr c d e H1 H2 H3 Hs H4 H5 H6.
  pose proof H1 as [[[L1 _] _] _]. pose proof H2 as [[[L2 _] _] _]. pose proof H3 as [[W3 _] _].
  pose proof H4 as [[[L4 _] _] _]. pose proof H5 as [[[L5 _] _] _]. pose proof H6 as [[[L6 _] _] _].
  pose proof (cells_bytes_length hdr W3) as L3. cbn [cell_wf] in L1, L2, L4, L5, L6.
  pose proof (rw_cells_join2 _ _ (A + (Z.of_nat n + 30) + Z.of_nat pad) _ _ H5 ltac:(cbn; lia) H6) as J.
  pose proof (rw_cells_join2 _ _ (A + (Z.of_nat n + 30)) _ _ H4 ltac:(cbn; lia) J) as J4.
  pose proof (rw_cells_join2 _ _ (A + 30) _ _ H3 ltac:(rewrite Hs; lia) J4) as J3.
  pose proof (rw_cells_join2 _ _ (A + 12) _ _ H2 ltac:(cbn; lia) J3) as J2.
  pose proof (rw_cells_join2 _ _ (A + 6) _ _ H1 ltac:(cbn; lia) J2) as J1.
  eapply rw_cells_rebytes; [exact J1 | |].
  - cbn [cells_wf cell_wf]. split; [|exact I]. rewrite !length_app. lia.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
Qed.

(* The cells of the buffer at 0x13970: the two MACs, the 18 bytes the stores write, the body,
   the pad, and the rest the function does not write. *)
Lemma out_split : forall m A (n pad : nat) l, (30 + n + pad <= length l)%nat ->
  rw_cells rsegs m A [CB (length l) l] ->
  (exists j, rw_cells rsegs m A [CB 6 j]) /\ (exists j, rw_cells rsegs m (A + 6) [CB 6 j]) /\
  (exists j, rw_cells rsegs m (A + 12) [CB 18 j]) /\ (exists j, rw_cells rsegs m (A + 30) [CB n j]) /\
  (exists j, rw_cells rsegs m (A + (Z.of_nat n + 30)) [CB pad j]) /\
  rw_cells rsegs m (A + (Z.of_nat n + 30) + Z.of_nat pad)
    [CB (length l - (30 + n + pad)) (skipn (30 + n + pad) l)].
Proof.
  intros m A n pad l Hle H.
  replace (length l) with (6 + (length l - 6))%nat in H by lia.
  apply rw_cb_split in H. destruct H as [H1 H]. split; [eexists; exact H1|].
  replace (length l - 6)%nat with (6 + (length l - 12))%nat in H by lia.
  apply rw_cb_split in H. destruct H as [H2 H].
  split; [eexists; replace (A + 6) with (A + Z.of_nat 6) by lia; exact H2|].
  replace (length l - 12)%nat with (18 + (length l - 30))%nat in H by lia.
  apply rw_cb_split in H. destruct H as [H3 H].
  split; [eexists; replace (A + 12) with (A + Z.of_nat 6 + Z.of_nat 6) by lia; exact H3|].
  replace (length l - 30)%nat with (n + (length l - (30 + n)))%nat in H by lia.
  apply rw_cb_split in H. destruct H as [H4 H].
  split; [eexists; replace (A + 30) with (A + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 18) by lia; exact H4|].
  replace (length l - (30 + n))%nat with (pad + (length l - (30 + n + pad)))%nat in H by lia.
  apply rw_cb_split in H. destruct H as [H5 H].
  split; [eexists; replace (A + (Z.of_nat n + 30)) with (A + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 18 + Z.of_nat n) by lia; exact H5|].
  replace (A + (Z.of_nat n + 30) + Z.of_nat pad)
    with (A + Z.of_nat 6 + Z.of_nat 6 + Z.of_nat 18 + Z.of_nat n + Z.of_nat pad) by lia.
  rewrite !skipn_skipn in H.
  match type of H with context [skipn ?k l] => replace k with (30 + n + pad)%nat in H by lia end.
  exact H.
Qed.

(** * The sum loop 0x139cc..0x139d8 *)

Lemma firstn1_skipn : forall (l : list byte) i d, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l d].
Proof. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma sum_firstn_S : forall l i d, (i < length l)%nat ->
  sum_bytes (firstn (S i) l) = sum_bytes (firstn i l) + bz (nth i l d).
Proof.
  induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia.
  - cbn [firstn sum_bytes nth]. rewrite ?firstn_O. cbn [sum_bytes]. lia.
  - cbn [firstn sum_bytes nth]. rewrite (IH i d) by lia. lia.
Qed.

Lemma ne_wrap : forall x y, 0 < x < y -> y <= 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy. unfold bv_eqb. apply Z.eqb_neq. rewrite !unsigned_lit_wrap.
  rewrite (Z.mod_small x) by lia.
  destruct (Z.eq_dec y (2^64)) as [->|Ne]; [rewrite Z_mod_same_full; lia | rewrite Z.mod_small by lia; lia].
Qed.

(* 0x13918 .. 0x13924: seqz, snez, or and beqz of the body_len && !body test. *)
Lemma or_test_false : forall body n, 0 <= n < 2^64 -> (n = 0 \/ 0 < body < 2^64) ->
  bv_eqb (Z_to_bv 64 (Z.lor (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 body)))
                              (bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)))) (Z_to_bv 64 0) = false.
Proof.
  intros body n Hn Hc. unfold v_sltu, v_sltiu, c_ltu, bv_ltu.
  rewrite (unsigned_lit n) by lia.
  destruct Hc as [-> | Hb].
  - destruct (bv_unsigned (Z_to_bv 64 0) <? bv_unsigned (Z_to_bv 64 body)); vm_compute; reflexivity.
  - rewrite (unsigned_lit body) by lia. rewrite (unsigned_lit 0) by lia.
    replace (0 <? body) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (n <? bv_wrap 64 1); vm_compute; reflexivity.
Qed.

Ltac take_by b tac :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; tac]
  end.

(* The register leaves of the end state of an exit: evars, kept values, then sp and a0 (a closed
   code there, so vm_compute may decide it) by bv_eq. *)
Ltac fin_regs :=
  unfold mkR;
  repeat match goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal
  | |- Some _ = Some _ => f_equal
  end;
  try (apply bv_eq; usub; first [lia | vm_compute; reflexivity]).

Lemma zxb_u : forall b, bv_unsigned (zxb b) = bz b.
Proof. intros b. unfold zxb, bz. apply unsigned_lit. pose proof (bz_range b). unfold bz in *. lia. Qed.

(* diginet_sum16's loop: a0 sums the bytes, a2 walks from body to body + body_len (a1). *)
Lemma sum_loop : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (body : Z) (bb : list byte) (i : nat),
  bytes_at rsegs m body bb -> (i < length bb)%nat ->
  a0 = Z_to_bv 64 (sum_bytes (firstn i bb)) -> a1 = Z_to_bv 64 (body + Z.of_nat (length bb)) ->
  a2 = Z_to_bv 64 (body + Z.of_nat i) ->
  (forall a0' a2' a3' : word, a0' = Z_to_bv 64 (sum_bytes bb) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                          t3 t4 t5 t6) F (Z_to_bv 64 0x139dc) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6) F (Z_to_bv 64 0x139cc) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m body bb i BB Hi E0 E1 E2 K.
  pose proof (bytes_at_bound _ _ _ _ BB) as RB.
  remember (length bb - i)%nat as k eqn:Hk.
  revert i a0 a2 a3 Hi E0 E2 Hk.
  induction k as [|k IH]; intros i a0 a2 a3 Hi E0 E2 Hk; [lia|].
  subst a0 a1 a2.
  assert (RD : ov_read_bytes rsegs m (wa (body + Z.of_nat i)) 1 = Some [nth i bb (b8 0)]).
  { rewrite (bytes_at_read rsegs m body bb (Z.of_nat i) 1 BB) by lia.
    rewrite Nat2Z.id. f_equal. apply firstn1_skipn. exact Hi. }
  step. step. step. step.
  destruct (Nat.eq_dec (S i) (length bb)) as [Last|More].
  - take_by false ltac:(replace (body + Z.of_nat i + 1) with (body + Z.of_nat (length bb)) by lia;
                        unfold bv_eqb; rewrite Z.eqb_refl; reflexivity).
    eapply K.
    assert (SS : sum_bytes bb = sum_bytes (firstn i bb) + bz (nth i bb (b8 0))).
    { rewrite <- (sum_firstn_S bb i (b8 0)) by lia. rewrite Last, firstn_all. reflexivity. }
    rewrite SS, zxb_u. reflexivity.
  - take_by true ltac:(rewrite ne_wrap by lia; reflexivity).
    eapply IH with (i := S i); [lia | | | lia].
    + rewrite (sum_firstn_S bb i (b8 0)) by lia. rewrite zxb_u. reflexivity.
    + f_equal. lia.
Qed.

(** * Facts the step tactics do not see *)

(* A fact under keep is out of reach of the step tactics and of lia: the disjointness facts,
   whose disjunctions make lia slow, and the facts on the memory at a fence, moved to the
   current memory with xport. *)
Definition keep (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (keep T) in H.

(* H2: the kept fact H on memory ms, moved to the memory mc of the fence MUf : munch W ms mc,
   WMf : wmono ms mc; tac exposes the disjointness fact the move needs. *)
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

(* An exit with a code under 0 after the frame is restored: the buffer keeps its bytes. *)
Ltac err_fin FR ST sp BC RWO MUS WMS D :=
  release_frame FR ST (bv_unsigned sp);
  let R := fresh "RWO" in
  xport RWO R MUS WMS ltac:(unfold keep in D);
  apply evt_done; do 15 eexists; split;
  [ f_equal; rewrite BC; fin_regs
  | split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
    unfold build_out; rewrite BC; exact R ].

Theorem diginet_frame_build_holds :
  diginet_body_check_contract -> memcpy_contract -> memset_contract -> diginet_frame_build_contract.
Proof.
  intros DBC MCPY MSET. unfold diginet_frame_build_contract, DIGINET_FRAME_BUILD.
  intros ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    out dst src hp body mode lo send ack retry cmd ncmds dmac smac bb oj
    HO Hdst Hsrc Hhp Hbody Hmode Hsend Hack Hretry Hcmd Hncmds Hhp64 Ldm BDM Lsm BSM BHP BB RWO
    Ddst Dsrc Dhp Dbody ST LO Dosp Ddsp Dssp Dhsp Dbsp MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (Z.of_N 64) with 64 in Rsp.
  pose proof (bytes_at_bound _ _ _ _ BDM) as Rdst. rewrite Ldm in Rdst.
  pose proof (bytes_at_bound _ _ _ _ BSM) as Rsrc. rewrite Lsm in Rsrc.
  pose proof (bytes_at_bound _ _ _ _ BB) as Rbb.
  pose proof (rw_cells_bound _ _ _ _ RWO) as Roj. cbn [cells_size csize] in Roj. rewrite Nat.add_0_r in Roj.
  pose proof ST as (Rlo & Rhi & _).
  assert (Rmode : 0 <= mode <= 1) by (destruct Hmode; lia).
  assert (ST0 : stk0 m lo (bv_unsigned sp)) by exact ST.
  pose proof (hdr_ro m hp send ack retry cmd ncmds Hsend Hack Hretry BHP) as HC. clear BHP.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (out, out + Z.of_nat (length oj))] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (* The fence of the frame and of the 144 bytes of diginet_body_check. *)
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp)] m) as MUS.
  pose proof (wmono_refl rsegs m) as WMS.
  hide Ddst. hide Dsrc. hide Dhp. hide Dbody. hide Dosp. hide Ddsp. hide Dssp. hide Dhsp. hide Dbsp. hide Hmode.
  hide BDM. hide BSM. hide BB. hide RWO. hide HC.
  carve_frame 96%nat ST.
  do 13 step.
  (* 0x138e0 .. 0x13924: the argument tests *)
  step. take false.
  step. step. take false.
  step. step. take false.
  step. step. take false.
  do 4 step. take false.
  do 7 step.
  take_by false ltac:(apply or_test_false; lia).
  (* 0x13928: body_len > DIGINET_MAX_BODY_LEN *)
  do 2 step.
  destruct (Z_lt_le_dec 1484 (Z.of_nat (length bb))) as [BIG|SMALL].
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -4)
      by (unfold build_code; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [reflexivity | lia]).
    err_fin FR ST sp BC RWO MUS WMS Dosp. }
  take true.
  (* 0x13938: diginet_body_check (body, body_len) *)
  do 3 step.
  xport BB BB1 MUS WMS ltac:(unfold keep in Dbsp).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  call DBC.
  { exact Hbody. }
  { exact BB1. }
  { rewrite USP. exact ST. }
  { rewrite USP. lia. }
  { rewrite USP. unfold keep in Dbsp. lia. }
  { exact MI. }
  lazymatch goal with H : stk _ _ lo _ |- _ => rewrite USP in H; rename H into ST end.
  (* 0x13944: the code of diginet_body_check *)
  rewrite body_check_spec. destruct (system_at bb) eqn:SA; cbv iota; step.
  { take false. do 2 step. do 14 step.
    assert (BC : build_code bb (Z.of_nat (length oj)) = -10)
      by (unfold build_code; rewrite SA; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia | reflexivity]).
    err_fin FR ST sp BC RWO MUS WMS Dosp. }
  take true.
  (* 0x13950 .. 0x13968: the frame length and the space test *)
  do 4 step.
  destruct (Z_lt_le_dec (Z.of_nat (length bb)) 30) as [N30|N30].
  1: assert (FL : frame_len (length bb) = 60) by (unfold frame_len; lia);
     take false; step; step.
  2: assert (FL : frame_len (length bb) = Z.of_nat (length bb) + 30) by (unfold frame_len; lia);
     take true; step.
  all: destruct (Z_lt_le_dec (Z.of_nat (length oj)) (frame_len (length bb))) as [CAPS|CAPOK].
  1,3: take false; do 2 step; do 14 step;
    assert (BC : build_code bb (Z.of_nat (length oj)) = -5)
      by (unfold build_code; rewrite SA; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|];
          destruct (Z.ltb_spec (Z.of_nat (length oj)) (frame_len (length bb))); [reflexivity | lia]);
    err_fin FR ST sp BC RWO MUS WMS Dosp.
  all: take true.
  (* 0x13970: the writes into the buffer. The facts the writes keep move from the entry memory
     here; the frame and the stack under it go under keep, and the fence MUO starts. *)
  all: xport RWO RWO1 MUS WMS ltac:(unfold keep in Dosp).
  all: xport BDM BDM1 MUS WMS ltac:(unfold keep in Ddsp).
  all: xport BSM BSM1 MUS WMS ltac:(unfold keep in Dssp).
  all: xport HC HC1 MUS WMS ltac:(unfold keep in Dhsp).
  all: xport BB BB2 MUS WMS ltac:(unfold keep in Dbsp).
  all: clear MUS WMS BDM BSM HC BB RWO Ddsp Dssp Dhsp Dbsp.
  all: hide BDM1; hide BSM1; hide HC1; hide BB2.
  all: destruct (stk_split rsegs _ lo (bv_unsigned sp - 240) (bv_unsigned sp + -96) ST ltac:(lia)) as [STl STm];
    clear ST STl; hide STm; hide FR.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
         pose proof (munch_refl [(out, out + Z.of_nat (length oj))] mc) as MUO;
         pose proof (wmono_refl rsegs mc) as WMO end.
  all: destruct (out_split _ out (length bb) (30 - length bb) oj ltac:(lia) RWO1)
         as ((j1 & P1) & (j2 & P2) & (j3 & P3) & (j4 & P4) & (j5 & P5) & P6); clear RWO1.
  (* 0x13970: memcpy (buf, dst, 6) *)
  all: do 4 step.
  all: xport BDM1 BDM2 MUO WMO ltac:(unfold keep in Ddst).
  all: assert (UO : bv_unsigned (Z_to_bv 64 out) = out) by (apply unsigned_lit; lia).
  all: assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  all: assert (UD : bv_unsigned (Z_to_bv 64 dst) = dst) by (apply unsigned_lit; lia).
  all: call MCPY; [ rewrite UD; exact BDM2 | rewrite Ldm; reflexivity | rewrite UO; exact P1
                  | rewrite UD, UO, U6; unfold keep in Ddst; lia | assumption | ].
  all: lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  all: lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
         rewrite UO, U6 in H; change (Z.to_nat 6) with 6%nat in H; rename H into Q1 end.
  (* 0x13980: memcpy (buf + 6, src, 6) *)
  all: do 4 step.
  all: xport BSM1 BSM2 MUO WMO ltac:(unfold keep in Dsrc).
  all: assert (UO6 : bv_unsigned (Z_to_bv 64 (out + 6)) = out + 6) by (apply unsigned_lit; lia).
  all: assert (US : bv_unsigned (Z_to_bv 64 src) = src) by (apply unsigned_lit; lia).
  all: call MCPY; [ rewrite US; exact BSM2 | rewrite Lsm; reflexivity | rewrite UO6; exact P2
                  | rewrite US, UO6, U6; unfold keep in Dsrc; lia | assumption | ].
  all: lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end.
  all: lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
         rewrite UO6, U6 in H; change (Z.to_nat 6) with 6%nat in H; rename H into Q2 end.
  all: clear BDM1 BSM1 Ddst Dsrc.
  (* 0x13990 .. 0x139b4: EtherType and numbytes *)
  all: do 10 step.
  (* 0x139b8: the sum, when body_len is not 0 and the mode is DIGINET_SUM_BODY *)
  all: step.
  1: destruct (Nat.eq_dec (length bb) 0) as [N0|N0]; [take true | take false].
  3: assert (N0 : length bb <> 0%nat) by lia; take false.
  2,3: unfold keep in Hmode; step; destruct Hmode as [M|M]; [take false | take true].
  (* goals: n = 0; n in 1..29 with mode 0, mode 1; n >= 30 with mode 0, mode 1 *)
  2,4: do 3 step; xport BB2 BB3 MUO WMO ltac:(unfold keep in Dbody);
       eapply sum_loop with (i := 0%nat);
       [ exact BB3 | lia | rewrite firstn_O; reflexivity | first [reflexivity | f_equal; usub; lia]
       | f_equal; lia | ];
       intros a0' a2' a3' EA0; subst a0'; clear BB3; step.
  (* 0x139e0 .. 0x13a44: the sum, the counters, retry, cmd and num_commands *)
  all: do 2 step.
  all: xport HC1 HC2 MUO WMO ltac:(unfold keep in Dhp); unfold keep in Dhp.
  all: do 24 step.
  all: clear HC2 HC1; hide Dhp.
  (* 0x13a48: memcpy (buf + 30, body, body_len) when body_len is not 0 *)
  all: step; first [take true | take false].
  (* body_len = 0: the body cell is empty *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 80484) _ _ _ _) =>
           pose proof P4 as [[[L4 _] _] _]; cbn [cell_wf] in L4;
           replace j4 with bb in P4 by (destruct bb; [| cbn in N0; lia]; destruct j4; [reflexivity | cbn in L4; lia]);
           clear L4
       | _ => idtac
       end.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 80460) _ _ _ _) =>
           do 4 step;
           xport BB2 BB4 MUO WMO ltac:(unfold keep in Dbody);
           assert (U30 : bv_unsigned (Z_to_bv 64 (out + 30)) = out + 30) by (apply unsigned_lit; lia);
           assert (UB : bv_unsigned (Z_to_bv 64 body) = body) by (apply unsigned_lit; lia);
           assert (Un : bv_unsigned (Z_to_bv 64 (Z.of_nat (length bb))) = Z.of_nat (length bb))
             by (apply unsigned_lit; lia);
           call MCPY;
           [ rewrite UB; exact BB4 | rewrite Un, Nat2Z.id; reflexivity | rewrite U30, Un, Nat2Z.id; exact P4
           | rewrite UB, U30, Un; unfold keep in Dbody; lia | assumption | ];
           lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ => clear H end;
           lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
             rewrite U30, Un, Nat2Z.id in H end;
           do 2 step; first [take true | take false]
       | _ => idtac
       end.
  (* body_len >= 30: no pad *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 80504) _ _ _ _) =>
           pose proof P5 as [[[L5 _] _] _]; cbn [cell_wf] in L5;
           replace j5 with (repeat (b8 0) (30 - length bb)) in P5
             by (replace (30 - length bb)%nat with 0%nat in * by lia; destruct j5; [reflexivity | cbn in L5; lia]);
           clear L5
       | _ => idtac
       end.
  (* 0x13a64: memset (buf + len, 0, out - len) *)
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 80484) _ _ _ _) =>
           do 5 step; usub;
           assert (UA : bv_unsigned (Z_to_bv 64 (out + (Z.of_nat (length bb) + 30)))
                        = out + (Z.of_nat (length bb) + 30)) by (apply unsigned_lit; lia);
           assert (UP : bv_unsigned (Z_to_bv 64 (30 - Z.of_nat (length bb))) = 30 - Z.of_nat (length bb))
             by (apply unsigned_lit; lia);
           assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity;
           assert (ZP : Z.to_nat (30 - Z.of_nat (length bb)) = (30 - length bb)%nat) by lia;
           call MSET; [ rewrite UA, UP, ZP; exact P5 | assumption | ];
           lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 _)) _ |- _ =>
             rewrite UA, UP, ZP, U0 in H; change (Z_to_bv 8 (0 mod 256)) with (b8 0) in H end
       | _ => idtac
       end.
  (* 0x13a78: the buffer, the stack under the frame and the frame for the epilogue *)
  all: lazymatch goal with H4 : rw_cells _ _ (_ + 30) _, H5 : rw_cells _ _ (_ + (_ + 30)) _ |- _ =>
         pose proof (join6 _ _ _ _ _ _ _ _ _ _ _ Q1 Q2 P3 eq_refl H4 H5 P6) as J end.
  all: pose proof (stk_rebuild m _ lo (bv_unsigned sp - 240) _ _ _ _ _
                     (proj1 (stk_split rsegs m lo (bv_unsigned sp - 240) (bv_unsigned sp) ST0 ltac:(lia)))
                     MU WM ltac:(lia) J ltac:(cbn [cells_size csize]; lia)) as STl.
  all: xport STm STm1 MUO WMO ltac:(unfold keep in Dosp).
  all: pose proof (stk_merge rsegs _ _ _ _ STl STm1 ltac:(lia)) as ST.
  all: xport FR FR1 MUO WMO ltac:(unfold keep in Dosp).
  all: clear STl STm1.
  all: do 14 step.
  all: release_frame FR1 ST (bv_unsigned sp).
  all: assert (BC : build_code bb (Z.of_nat (length oj)) = frame_len (length bb))
         by (unfold build_code; rewrite SA; destruct (Z.ltb_spec 1484 (Z.of_nat (length bb))); [lia|];
             destruct (Z.ltb_spec (Z.of_nat (length oj)) (frame_len (length bb))); [lia | reflexivity]).
  (* the bytes of the buffer *)
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
         assert (RWF : rw_cells rsegs mc out [CB (length oj) (build_out dmac smac send ack retry cmd ncmds bb mode oj)])
       end.
  1,3,5,7,9:
    eapply rw_cells_rebytes; [exact J | |];
    unfold build_out; cbv zeta; rewrite BC;
    replace (0 <=? frame_len (length bb)) with true by (symmetry; apply Z.leb_le; lia); cbv iota;
    [ cbn [cells_wf cell_wf]; split; [|exact I]; rewrite length_app, length_skipn;
      pose proof (length_build_frame dmac smac send ack retry cmd ncmds bb (mode =? 1) Ldm Lsm); lia
    | rewrite !cb1_bytes;
      rewrite (frame_bytes_eq dmac smac send ack retry cmd ncmds bb mode (repeat (b8 0) (30 - length bb)) _ eq_refl);
      apply (f_equal2 (@app byte)); [reflexivity|];
      apply (f_equal2 (@app byte)); [reflexivity|];
      apply (f_equal2 (@app byte));
      [ apply hdr_eq; [lia | lia | lia | lia | |];
        first
          [ assert (SV0 : (if mode =? 1 then 0 else spec_sum bb) = 0)
              by (first [ rewrite M; reflexivity
                        | destruct (mode =? 1); [reflexivity | destruct bb; [reflexivity | cbn in N0; lia]] ]);
            rewrite SV0; apply bv_eq; vm_compute; reflexivity
          | first [rewrite z8_sum_hi | rewrite z8_sum_lo]; rewrite M; change (0 =? 1) with false; cbv iota;
            rewrite spec_sum_eq; reflexivity ]
      | apply (f_equal2 (@app byte)); [reflexivity|];
        apply (f_equal2 (@app byte)); [reflexivity|];
        apply (f_equal (fun k => skipn k oj)); lia ] ].
  (* the registers: a0 (sext.w of s8, 60 or the uncut length + 30) is build_code bb cap *)
  all: try (replace (Z_to_bv 64 60) with (Z_to_bv 64 (build_code bb (Z.of_nat (length oj))))
              by (rewrite BC, FL; reflexivity)).
  all: try (match goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
         match R with context [Z_to_bv 64 (bv_swrap 32 ?x)] =>
           replace (Z_to_bv 64 (bv_swrap 32 x)) with (Z_to_bv 64 (build_code bb (Z.of_nat (length oj))))
             by (rewrite BC; usub; rewrite ?Z.add_0_r; rewrite swrap32_small by lia; apply bv_eq; usub; lia)
         end end).
  all: apply evt_done; do 15 eexists; split; [reflexivity|].
  all: split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; exact RWF.
Qed.
