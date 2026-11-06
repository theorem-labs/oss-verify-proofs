(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_braid: the braid relation that both callees of image B's LLVMFuzzerTestOneInput
   segment crt1 take, derived from what the decode leaf left:

     check_round_trip_cg.v dec_crt_braid (aview segs (w_H W) mem) (copy + 50) buffer nch ns

   from `garr8 ... copy (the frame bytes)` and `garr8 ... buffer (CDec.braid_out body nch ns)`, i.e. from the two
   clauses of llvm_b_st_5cc that reac_decode's contract (lib/B/Prog/reac_decode_cg.v) left.  check_braid's own
   premise `braid_map` is the same relation at decode's reader, so the exit lane's call site uses this file too.

   PORT of the old footprint-era record on a working branch at 3ee4cb94cb5:
   proofs/libreac/fuzz_decode/lib/B/Prog/afd_down_scan.v:1872 ads_braid_pos, :1887 ads_braid_len, :1890
   ads_braid_nth, :1921 ads_braid_map (the same statement over decode's blk_data / mrd instead of cgif's
   garr8 / aview).  No new proof idea; the index algebra is that file's. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YM05 YK04 YA0i YA0n YP09 YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_decode_c check_braid_c.
Import ListNotations.
Open Scope Z_scope.
(* lib/Reusable/YM03.v:182-189 redefines lia / nia globally; this file uses the plain ones (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_decode_c.
Module DCBc := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_braid_c.

(* Z.even is the low bit (the two sources write the same test differently). *)
Lemma c1b_even_mod : forall ch, Z.even ch = (ch mod 2 =? 0).
Proof.
  intros ch. destruct (Z.even ch) eqn:E.
  - apply Z.even_spec in E as [k ->]. symmetry. apply Z.eqb_eq.
    rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - symmetry. apply Z.eqb_neq. intros H.
    apply Z.mod_divide in H; [|lia]. destruct H as [k ->].
    rewrite Z.even_mul in E. cbn in E. rewrite Bool.orb_true_r in E. discriminate.
Qed.

(* afd_down_scan.v:1872 ads_braid_pos: reac_decode's index of the payload byte of (s, ch, j) and check_braid's
   offset of the same byte are the same one. *)
Lemma c1b_braid_pos : forall s ch nch j, 0 <= ch -> 0 <= j < 3 ->
  CDec.braid_pos s ch nch j = 3 * (s * nch + 2 * (ch / 2)) + DCBc.braid_off ch j.
Proof.
  intros s ch nch j Hch Hj.
  assert (Hd : ch - ch mod 2 = 2 * (ch / 2)).
  { pose proof (Z.div_mod ch 2 ltac:(lia)) as D. lia. }
  unfold CDec.braid_pos, DCBc.braid_off. cbv zeta. rewrite c1b_even_mod, Hd.
  assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct (Z.eqb_spec (ch mod 2) 0) as [E | E];
    destruct Hj3 as [ -> | [ -> | -> ] ]; cbn; lia.
Qed.

(* afd_down_scan.v:1887 ads_braid_len. *)
Lemma c1b_braid_len : forall bs nch ns, length (CDec.braid_out bs nch ns) = Z.to_nat (3 * nch * ns).
Proof. intros bs nch ns. unfold CDec.braid_out. rewrite !length_map, length_seq. reflexivity. Qed.

(* The k-th element of the index list of braid_out. *)
Lemma c1b_nth_seqZ : forall (N k : nat), (k < N)%nat -> nth k (map Z.of_nat (seq 0 N)) 0 = Z.of_nat k.
Proof.
  intros N k Hk.
  rewrite (nth_indep (map Z.of_nat (seq 0 N)) 0 (Z.of_nat 0))
    by (rewrite length_map, length_seq; exact Hk).
  rewrite (map_nth Z.of_nat (seq 0 N) 0%nat k).
  rewrite seq_nth by exact Hk. reflexivity.
Qed.

(* The k-th byte of braid_out is braid_byte at index k. *)
Lemma c1b_braid_nth : forall bs nch ns (k : nat), (k < Z.to_nat (3 * nch * ns))%nat ->
  nth k (CDec.braid_out bs nch ns) (Z_to_bv 8 0) = CDec.braid_byte bs nch ns (Z.of_nat k).
Proof.
  intros bs nch ns k Hk. unfold CDec.braid_out.
  rewrite (nth_indep (map (CDec.braid_byte bs nch ns) (map Z.of_nat (seq 0 (Z.to_nat (3 * nch * ns)))))
             (Z_to_bv 8 0) (CDec.braid_byte bs nch ns 0))
    by (rewrite !length_map, length_seq; exact Hk).
  rewrite (map_nth (CDec.braid_byte bs nch ns) (map Z.of_nat (seq 0 (Z.to_nat (3 * nch * ns)))) 0 k).
  f_equal.
  apply c1b_nth_seqZ. exact Hk.
Qed.

(* The one byte of a one-byte cell. *)
Lemma c1b_le_byte1 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 (le_byte v 1 0)) = v.
Proof.
  intros v Hv. unfold le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  rewrite Z.mod_mod by lia. rewrite Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.

(* A byte list read through garr8 is read through cgif's aview. *)
Lemma c1b_garr8_view : forall (W : world decodesegsB0) (mem : word -> option byte) base (l : list Z) (k : nat),
  garr8 decodesegsB0 (mrestrict (w_H W) mem) base l -> (k < length l)%nat ->
  aview decodesegsB0 (w_H W) mem (base + Z.of_nat k) = Some (nth k l 0).
Proof.
  intros W mem base l k G Hk. destruct (G k Hk) as [V R].
  specialize (V 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in V. rewrite Z.add_0_r in V.
  unfold aview. rewrite V. cbn [option_map]. f_equal.
  exact (c1b_le_byte1 (nth k l 0) R).
Qed.

Lemma c1b_nth_map_bv : forall (l : list byte) (k : nat),
  nth k (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof. intros l k. exact (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) k). Qed.

(* afd_down_scan.v:1921 ads_braid_map, at cgif's reader: what reac_decode left in the buffer is the braid of the
   frame's audio region, which is what check_round_trip and check_braid read.  The frame only has to reach past the
   last braided byte (50 + 3 nch ns + 1 bytes), so the exit segment's upstream frame (52 + 36 nch bytes) uses it too. *)
Lemma c1b_braid_of_garr8 :
  forall (W : world decodesegsB0) (mem : word -> option byte) (body : list byte) (res out nch ns : Z),
  0 < nch -> 0 < ns -> 51 + 3 * nch * ns <= Z.of_nat (length body) ->
  garr8 decodesegsB0 (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) body) ->
  garr8 decodesegsB0 (mrestrict (w_H W) mem) out
    (map (fun b : byte => bv_unsigned b) (CDec.braid_out body nch ns)) ->
  dec_crt_braid (aview decodesegsB0 (w_H W) mem) (res + 50) out nch ns.
Proof.
  intros W mem body res out nch ns Hn Hs Hlen G1 G2 ch s j Hch Hs' Hj.
  set (i := 3 * (ch * ns + s) + j).
  assert (Hi : 0 <= i < 3 * nch * ns) by (unfold i; nia).
  (* the buffer byte *)
  assert (Hk2 : (Z.to_nat i < length (map (fun b : byte => bv_unsigned b) (CDec.braid_out body nch ns)))%nat)
    by (rewrite length_map, c1b_braid_len; lia).
  pose proof (c1b_garr8_view W mem out _ (Z.to_nat i) G2 Hk2) as V2.
  rewrite Z2Nat.id in V2 by lia.
  rewrite c1b_nth_map_bv in V2.
  rewrite (c1b_braid_nth body nch ns (Z.to_nat i)) in V2 by lia.
  rewrite Z2Nat.id in V2 by lia.
  (* the index of the frame byte the braid takes it from *)
  assert (Hdiv : i / 3 = ch * ns + s).
  { unfold i. replace (3 * (ch * ns + s) + j) with ((ch * ns + s) * 3 + j) by lia.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (Hmod : i mod 3 = j).
  { unfold i. replace (3 * (ch * ns + s) + j) with (j + (ch * ns + s) * 3) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  assert (Hq : (ch * ns + s) / ns = ch).
  { rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (Hr : (ch * ns + s) mod ns = s).
  { replace (ch * ns + s) with (s + ch * ns) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  unfold CDec.braid_byte in V2. rewrite Hdiv, Hmod, Hq, Hr in V2.
  set (p := CDec.braid_pos s ch nch j) in *.
  assert (Hp0 : 0 <= p).
  { unfold p. rewrite c1b_braid_pos by lia. pose proof (Z.div_pos ch 2 ltac:(lia)).
    unfold DCBc.braid_off. destruct (Z.even ch); destruct (j =? 0), (j =? 1); nia. }
  assert (Hsc : s * nch + ch <= nch * ns - 1) by nia.
  assert (Hp1 : 50 + p <= Z.of_nat (length body) - 1).
  { unfold p. rewrite c1b_braid_pos by lia.
    pose proof (Z.div_mod ch 2 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm2.
    unfold DCBc.braid_off. rewrite c1b_even_mod.
    destruct (Z.eqb_spec (ch mod 2) 0) as [E0 | E0].
    - replace (2 * (ch / 2)) with ch by lia.
      destruct (j =? 0), (j =? 1); nia.
    - replace (2 * (ch / 2)) with (ch - 1) by lia.
      destruct (j =? 0), (j =? 1); nia. }
  (* the frame byte *)
  assert (Hk1 : (Z.to_nat (50 + p) < length (map (fun b : byte => bv_unsigned b) body))%nat)
    by (rewrite length_map; lia).
  pose proof (c1b_garr8_view W mem res _ (Z.to_nat (50 + p)) G1 Hk1) as V1.
  rewrite Z2Nat.id in V1 by lia.
  rewrite c1b_nth_map_bv in V1.
  exists (bv_unsigned (nth (Z.to_nat (50 + p)) body (Z_to_bv 8 0))).
  split.
  - replace (out + 3 * (ch * ns + s) + j) with (out + i) by (unfold i; lia). exact V2.
  - replace (res + 50 + 3 * (s * nch + 2 * (ch / 2)) + DCBc.braid_off ch j) with (res + (50 + p))
      by (unfold p; rewrite c1b_braid_pos by lia; lia).
    exact V1.
Qed.
