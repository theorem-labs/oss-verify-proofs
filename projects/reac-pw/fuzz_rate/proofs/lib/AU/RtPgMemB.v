(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgMem.v at 37d45827ae9e, ported to reac-pw/fuzz_rate
   image A: module paths and the prefix (rm_ -> rtm_, RPgBase's rl_ -> RtPgBase's rt_) changed; the frame for locals is
   rate's (seven objects, 56 shadow bytes, fifteen store sites); risk 2 is shown at rate's site 0x808f0, where the
   region route is also run through the symbolic engine (rtm_A_808f0_step, new); the lemmas for an n-byte access
   inside one granule (rtm_ra_cell_n, rtm_ra_slow_n_bv, rtm_ra_cell4) and for a block's partial last granule
   (rtm_blk_last) are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgMem.v at 03123c602bdd, ported to image B
   (fuzz_rate.asan-ubsan): prefix rtm_ -> rtmb_ (rtm_A_ -> rtmb_B_), image B's segments and record (RtPgImgB); the frame
   for locals is image B's (class 4, seven objects t ch r e e42 e62 hz, 88 shadow bytes, sixteen store groups; no asked
   objects); the real-frame range R+0x198 (16); risk 2 at image B's site 0x809d8 and the slow-block variant at 0x80fcc
   (rtmb_B_80fcc_step, new); the asked[] cell lemmas rtmb_ask_join / rtmb_ask_split are new. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; addresses measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the memory and shadow layer of
   the walk of LLVMFuzzerTestOneInput (0x8076c). Proves no function (kind: segment lemma). Every lemma is over the
   concrete state (aview, val_mem, garr8, the shadow bytes), generic in the segments segs, so that each walk piece can
   rebuild its symbolic regions from a cut's facts and give the facts back after its run, a store or a call.

   1. Byte lists: the little-endian value of a byte list and its bytes (le_byte), the bytes of Z_to_le_bytes.
   2. rtmb_bytes: a list of bytes at an address, the form of rate_build_contract's and rate_check_contract's garr8
      premises (pp's image, the input after the 7-byte header); kept, split, slice, patch (a store or a call's write
      inside the list), the value of a field, the bytes a store leaves; the fields of pp's image (len, is_props,
      has_params, params_struct, ent[i], n_ent, corrupt, buf) as the code loads them; read-only image bytes.
   3. Calls: what __asan_memset / __asan_memcpy leave (the memory part of YG0d.aintrin_realizes' post); the shadow
      premises of a block's bytes (pp, pod, buf, the input), and the shadow byte of a block's partial last granule
      (buf's bl' = buflen + (buflen = 0) in [1, 23]; the input's).
   4. Shadow checks. The engine's token path (lib/Reusable/YCbn.v tok_branch) follows a check's slow block only when
      it starts at the `bnez` target or at the `beqz` fall-through. Over the 113 instrumented checks of image B's
      LLVMFuzzerTestOneInput: 62 are `bnez t,L` with L = `andi u,x,7; [addi u,u,k]; blt u,t,back` (both outcomes
      followed), 24 are `beqz t,+8; j L` with a slow block L (19 `andi u,x,7; bge u,t,report; j back`, 5 `andi u,x,7;
      blt u,t,+8; j report; j back`), 18 are `beqz t,+8; j report` and 9 are `bnez t,report`. For the `beqz; j` forms
      the token path takes its None arm, which asks shadow 0 over the whole granule. That holds for every check except
      seven input reads whose granule can be the input's last, partial one: 0x809d8, 0x80a0c, 0x80a80 (E01: header
      bytes 0, 1, 2), 0x80b18, 0x80b68 (M01.pre), 0x80fcc (P.sel), 0x81360 (P.struct_open_count). There the walk puts
      the input's shadow byte in a region (rtmb_cell_region) and loads it as memory, splits the `beqz` and the slow
      block's branch, and rtmb_ra_cell / rtmb_ra_slow(_bv) kill the report arm; rtmb_ra_gran_false records why the
      token path's obligation cannot be paid there; section 8 checks the code and the facts at 0x809d8 and runs the
      route at 0x809d8 and at 0x80fcc (the one input read whose slow block is the `blt; j report; j back` form).
      rtmb_ra_cell_n gives the shadow byte of an n-byte access inside one granule (the `bnez` checks of floats[20],
      closed_list[2], r[k]).
   5. The stack's zero shadow: the real-frame cells the code shadow-checks (parts[1]'s store8 check 0x81674 at R+0x1a0,
      pod_nearest's out cell at R+0x198) from AR's zero-shadow ranges.
   6. The frame for locals F (class 4, request 704 in a 1024-byte frame; the prologue writes 88 of its 128 shadow
      bytes from shadow_addr F): t F+0x20 (96 bytes), ch F+0xa0 (24), r F+0xe0 (4), e F+0xf0 (104), e42 F+0x180 (104),
      e62 F+0x210 (104), hz F+0x2a0 (4). rtmb_sh gives its shadow bytes in each scope state (the prologue's 88 stores
      0x80850-0x809b0 and the scope-store groups after it); the checks and calls on the seven objects (r and hz see
      the shadow byte 0x04 and pass on the slow path); the frame-shadow region's chunks.
   7. The real frame's 8-byte cells (R = s1) and RtPgBase's cut facts (rt_at / rt_cut): kept across a step, a store
      or a call, and as engine chunks; asked[0] / asked[1] as two 4-byte cells at R+0x198 / R+0x19c or one 8-byte cell.
   8. Risk 2 at 0x809d8, on image B's code: the token path's obligation, the site's facts, and the region route
      run through the symbolic engine from 0x809d0 to 0x809e4 (rtmb_B_809d8_step); the same route over the
      `blt; j report; j back` slow block at 0x80fcc, from 0x80fc4 to 0x80fd8, with an unaligned cursor
      (rtmb_B_80fcc_step).
   9. A segment's start facts at the current memory (input bytes, their shadow bytes and hull, rom_view) across a
      write set, and the address facts that keep the input's shadow bytes out of it (the shadow band, P0's bytes). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP03.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP02.
From OSSVerify.reac_pw.fuzz_rate.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* image B's loaded segments *)
Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== 1. byte lists ======================================== *)
Definition rtmb_slice (l : list byte) (o n : nat) : list byte := firstn n (skipn o l).

Lemma rtmb_lor_shift8 : forall a r, 0 <= a < 256 -> 0 <= r -> Z.lor a (Z.shiftl r 8) = a + 256 * r.
Proof.
intros a r Ha Hr.
assert (HL : Z.land a (Z.shiftl r 8) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z_lt_le_dec n 8) as [Hl|Hg].
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.bits_0; reflexivity|].
    rewrite Z.bits_above_log2; [reflexivity | lia |].
    assert (Z.log2 a < 8) by (apply Z.log2_lt_pow2; lia). lia. }
rewrite <- Z.lxor_lor by exact HL. rewrite <- Z.add_nocarry_lxor by exact HL.
rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.

Lemma rtmb_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma rtmb_lez_range : forall l, 0 <= bytes_le_to_Z l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
induction l as [|b l IH]; [cbn; lia|].
cbn [bytes_le_to_Z length]. pose proof (rtmb_byte_range b) as Hb.
rewrite rtmb_lor_shift8 by lia.
rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. nia.
Qed.

Lemma rtmb_lez_cons : forall b l, bytes_le_to_Z (b :: l) = bv_unsigned b + 256 * bytes_le_to_Z l.
Proof.
intros b l. cbn [bytes_le_to_Z]. pose proof (rtmb_lez_range l). apply rtmb_lor_shift8; [apply rtmb_byte_range | lia].
Qed.

Lemma rtmb_lez_shiftr : forall l k, (k < length l)%nat ->
Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
induction l as [|b l IH]; intros k Hk; cbn [length] in Hk; [lia|].
rewrite rtmb_lez_cons. pose proof (rtmb_byte_range b) as Hb. pose proof (rtmb_lez_range l) as Hl.
destruct k as [|k].
- cbn [nth]. rewrite Nat2Z.inj_0, Z.mul_0_r, Z.shiftr_0_r.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. exact Hb.
- cbn [nth]. rewrite Nat2Z.inj_succ, Z.mul_succ_r.
  replace (8 * Z.of_nat k + 8) with (8 + 8 * Z.of_nat k) by lia.
  rewrite <- Z.shiftr_shiftr by lia. rewrite (Z.shiftr_div_pow2 _ 8) by lia. change (2 ^ 8) with 256.
  replace ((bv_unsigned b + 256 * bytes_le_to_Z l) / 256) with (bytes_le_to_Z l).
  + apply IH. lia.
  + rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma rtmb_lez_le_byte : forall l k, (k < length l)%nat ->
le_byte (bytes_le_to_Z l) (length l) k = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
intros l k Hk. unfold le_byte. rewrite (Z.mod_small (bytes_le_to_Z l)) by apply rtmb_lez_range.
apply rtmb_lez_shiftr. exact Hk.
Qed.

Lemma rtmb_le_byte_bv : forall v n k, (k < n)%nat ->
Z_to_bv 8 (le_byte v n k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
intros v n k Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). unfold le_byte. change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 8) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma rtmb_nth_le_bytes : forall n v k, (k < n)%nat ->
nth k (Z_to_le_bytes n v) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros v k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- rewrite Nat2Z.inj_0, Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma rtmb_nth_map : forall (l : list byte) j,
nth j (map (fun x : byte => bv_unsigned x) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|b l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma rtmb_nth_repeat : forall (x d : byte) n i, (i < n)%nat -> nth i (repeat x n) d = x.
Proof. intros x d n. induction n as [|n IH]; intros [|i] Hi; cbn [repeat nth]; [lia | lia | reflexivity | apply IH; lia]. Qed.

Lemma rtmb_length_repeat : forall (x : byte) n, length (repeat x n) = n.
Proof. intros x n. induction n as [|n IH]; cbn [repeat length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rtmb_unsigned_byte : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma rtmb_le_byte_1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* ==================================== 2. bytes at an address ==================================== *)
Definition rtmb_bytes (H : word -> bool) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
garr8 segs (mrestrict H mem) a (map (fun x : byte => bv_unsigned x) l).

Lemma rtmb_val1_aview : forall H mem x v,
val_mem segs (mrestrict H mem) x 1 v -> 0 <= v < 256 -> aview segs H mem x = Some v.
Proof.
intros H mem x v V R. specialize (V 0%nat ltac:(lia)). rewrite Z.add_0_r in V.
unfold aview. rewrite V. cbn [option_map]. f_equal. rewrite rtmb_unsigned_byte, rtmb_le_byte_1 by exact R.
apply Z.mod_small. exact R.
Qed.

Lemma rtmb_aview_mbyte : forall H mem x (b : byte),
aview segs H mem x = Some (bv_unsigned b) -> mbyte segs (mrestrict H mem) x = Some b.
Proof.
intros H mem x b A. unfold aview in A. destruct (mbyte segs (mrestrict H mem) x) as [b'|] eqn:E; [|discriminate A].
cbn [option_map] in A. injection A as A. f_equal. apply bv_eq. exact A.
Qed.

Lemma rtmb_aview_val1 : forall H mem x v,
aview segs H mem x = Some v -> val_mem segs (mrestrict H mem) x 1 v /\ 0 <= v < 256.
Proof.
intros H mem x v A. unfold aview in A. destruct (mbyte segs (mrestrict H mem) x) as [b|] eqn:E; [|discriminate A].
cbn [option_map] in A. injection A as <-. pose proof (rtmb_byte_range b) as R. split; [|exact R].
intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, E, rtmb_le_byte_1 by exact R.
f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rtmb_bytes_aview : forall H mem a l,
rtmb_bytes H mem a l <->
(forall i, (i < length l)%nat -> aview segs H mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0)))).
Proof.
intros H mem a l. unfold rtmb_bytes, garr8. rewrite length_map. split.
- intros G i Hi. destruct (G i Hi) as [V R]. rewrite rtmb_nth_map in V, R. exact (rtmb_val1_aview _ _ _ _ V R).
- intros A i Hi. rewrite rtmb_nth_map. exact (rtmb_aview_val1 _ _ _ _ (A i Hi)).
Qed.

Lemma rtmb_bytes_kept : forall H mem H' mem' a l,
rtmb_bytes H mem a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview segs H' mem' x = aview segs H mem x) ->
rtmb_bytes H' mem' a l.
Proof.
intros H mem H' mem' a l B K. apply rtmb_bytes_aview. intros i Hi. rewrite K by lia.
exact (proj1 (rtmb_bytes_aview H mem a l) B i Hi).
Qed.

Lemma rtmb_bytes_app : forall H mem a l1 l2,
rtmb_bytes H mem a (l1 ++ l2) <-> rtmb_bytes H mem a l1 /\ rtmb_bytes H mem (a + Z.of_nat (length l1)) l2.
Proof. intros H mem a l1 l2. unfold rtmb_bytes. rewrite map_app, garr8_app, length_map. reflexivity. Qed.

Lemma rtmb_bytes_slice : forall H mem a l o n,
rtmb_bytes H mem a l -> (o + n <= length l)%nat -> rtmb_bytes H mem (a + Z.of_nat o) (rtmb_slice l o n).
Proof.
intros H mem a l o n B Hl. unfold rtmb_slice.
rewrite <- (firstn_skipn o l) in B. apply rtmb_bytes_app in B as [_ B].
rewrite length_firstn, Nat.min_l in B by lia.
rewrite <- (firstn_skipn n (skipn o l)) in B. apply rtmb_bytes_app in B as [B _]. exact B.
Qed.

Lemma rtmb_bytes_patch : forall H mem H' mem' a l o x,
rtmb_bytes H mem a l -> rtmb_bytes H' mem' (a + Z.of_nat o) x -> (o + length x <= length l)%nat ->
(forall y, a <= y < a + Z.of_nat (length l) -> ~ (a + Z.of_nat o <= y < a + Z.of_nat (o + length x)) ->
 aview segs H' mem' y = aview segs H mem y) ->
rtmb_bytes H' mem' a (Model.overwrite l o x).
Proof.
intros H mem H' mem' a l o x B X Hl K. unfold Model.overwrite.
assert (Lf : length (firstn o l) = o) by (rewrite length_firstn; lia).
rewrite <- (firstn_skipn o l) in B. apply rtmb_bytes_app in B as [B1 B2]. rewrite Lf in B2.
rewrite <- (firstn_skipn (length x) (skipn o l)) in B2. apply rtmb_bytes_app in B2 as [_ B3].
rewrite length_firstn, length_skipn, Nat.min_l in B3 by lia. rewrite skipn_skipn in B3.
apply rtmb_bytes_app. split.
- apply (rtmb_bytes_kept H mem); [exact B1|]. intros y Hy. rewrite Lf in Hy. apply K; lia.
- rewrite Lf. apply rtmb_bytes_app. split; [exact X|].
  replace (a + Z.of_nat o + Z.of_nat (length x)) with (a + Z.of_nat o + Z.of_nat (length x)) by reflexivity.
  replace (o + length x)%nat with (length x + o)%nat by lia.
  apply (rtmb_bytes_kept H mem); [exact B3|]. intros y Hy.
  rewrite length_skipn in Hy. apply K; lia.
Qed.

Lemma rtmb_bytes_val : forall H mem a l,
rtmb_bytes H mem a l -> val_mem segs (mrestrict H mem) a (length l) (bytes_le_to_Z l).
Proof.
intros H mem a l B k Hk. pose proof (proj1 (rtmb_bytes_aview H mem a l) B k Hk) as A.
rewrite (rtmb_aview_mbyte _ _ _ _ A). f_equal. rewrite rtmb_lez_le_byte by exact Hk.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rtmb_bytes_of_val : forall H mem a n v,
val_mem segs (mrestrict H mem) a n v -> rtmb_bytes H mem a (Z_to_le_bytes n v).
Proof.
intros H mem a n v V. apply rtmb_bytes_aview. intros i Hi. rewrite length_Z_to_le_bytes in Hi.
rewrite rtmb_nth_le_bytes by exact Hi. unfold aview. rewrite (V i Hi). cbn [option_map].
rewrite rtmb_le_byte_bv by exact Hi. reflexivity.
Qed.

Lemma rtmb_val_of_bytes : forall H mem a n v,
rtmb_bytes H mem a (Z_to_le_bytes n v) -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros H mem a n v B k Hk. pose proof (proj1 (rtmb_bytes_aview _ _ _ _) B k) as A.
rewrite length_Z_to_le_bytes in A. specialize (A Hk). rewrite rtmb_nth_le_bytes in A by exact Hk.
rewrite (rtmb_aview_mbyte _ _ _ _ A). rewrite rtmb_le_byte_bv by exact Hk. reflexivity.
Qed.

Lemma rtmb_bytes_field : forall H mem a l o n v,
rtmb_bytes H mem a l -> rtmb_slice l o n = Z_to_le_bytes n v -> (o + n <= length l)%nat ->
val_mem segs (mrestrict H mem) (a + Z.of_nat o) n v.
Proof.
intros H mem a l o n v B E Hl. apply rtmb_val_of_bytes. rewrite <- E. apply rtmb_bytes_slice; assumption.
Qed.

Lemma rtmb_bytes_byte : forall H mem a l c,
rtmb_bytes H mem a l -> (c < length l)%nat ->
val_mem segs (mrestrict H mem) (a + Z.of_nat c) 1 (bv_unsigned (nth c l (Z_to_bv 8 0))).
Proof.
intros H mem a l c B Hc. unfold rtmb_bytes, garr8 in B. rewrite length_map in B.
destruct (B c Hc) as [V _]. rewrite rtmb_nth_map in V. exact V.
Qed.

(* A store of the n-byte value v at a + o inside the list (a put32 / patch32 byte, a len8 store, a flag word). *)
Lemma rtmb_bytes_store : forall H mem H' mem' a l o n v,
rtmb_bytes H mem a l -> val_mem segs (mrestrict H' mem') (a + Z.of_nat o) n v -> (o + n <= length l)%nat ->
(forall y, a <= y < a + Z.of_nat (length l) -> ~ (a + Z.of_nat o <= y < a + Z.of_nat (o + n)) ->
 aview segs H' mem' y = aview segs H mem y) ->
rtmb_bytes H' mem' a (Model.overwrite l o (Z_to_le_bytes n v)).
Proof.
intros H mem H' mem' a l o n v B V Hl K.
apply (rtmb_bytes_patch H mem); [exact B | apply rtmb_bytes_of_val; exact V | rewrite length_Z_to_le_bytes; exact Hl |].
rewrite length_Z_to_le_bytes. exact K.
Qed.

(* ---- the fields of pp's image (Pod/Layout.v pp_image: buf, len, is_props, has_params, params_struct, ent[32],
   n_ent, corrupt) as the code loads them ---- *)
Section pp.
Variables (b : list byte) (isp hasp pst : bool) (es : list Model.ent) (corr : bool).
Hypothesis Hb : Z.of_nat (length b) <= Layout.POD_BUF_MAX.
Hypothesis He : (length es <= 32)%nat.
Hypothesis Hs : Forall (fun e => (length (Model.e_body e) <= 96)%nat) es.
Let IMG := Layout.pp_image b isp hasp pst es corr.
Lemma rtmb_pp_len_img : Z.of_nat (length IMG) = Layout.PP_SIZE.
Proof. unfold IMG. apply Layout.length_pp_image; assumption. Qed.

Lemma rtmb_pp_field : forall H mem pp off n v,
rtmb_bytes H mem pp IMG -> rtmb_slice IMG (Z.to_nat off) n = Z_to_le_bytes n v -> 0 <= off ->
off + Z.of_nat n <= Layout.PP_SIZE ->
val_mem segs (mrestrict H mem) (pp + off) n v.
Proof.
intros H mem pp off n v B E H0 H1. pose proof rtmb_pp_len_img as L.
replace (pp + off) with (pp + Z.of_nat (Z.to_nat off)) by lia.
apply (rtmb_bytes_field H mem pp IMG); [exact B | exact E | lia].
Qed.

Lemma rtmb_pp_len : forall H mem pp, rtmb_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_LEN) 8 (Z.of_nat (length b)).
Proof.
intros H mem pp B. apply (rtmb_pp_field H mem pp); [exact B | | unfold Layout.OFF_LEN; lia | unfold Layout.OFF_LEN, Layout.PP_SIZE; lia].
unfold rtmb_slice, IMG. eapply Layout.pp_read_len; eassumption.
Qed.
Lemma rtmb_pp_is_props : forall H mem pp, rtmb_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_IS_PROPS) 4 (Z.b2z isp).
Proof.
intros H mem pp B. apply (rtmb_pp_field H mem pp); [exact B | | unfold Layout.OFF_IS_PROPS; lia | unfold Layout.OFF_IS_PROPS, Layout.PP_SIZE; lia].
unfold rtmb_slice, IMG. eapply Layout.pp_read_is_props; eassumption.
Qed.
Lemma rtmb_pp_has_params : forall H mem pp, rtmb_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_HAS_PARAMS) 4 (Z.b2z hasp).
Proof.
intros H mem pp B. apply (rtmb_pp_field H mem pp); [exact B | | unfold Layout.OFF_HAS_PARAMS; lia | unfold Layout.OFF_HAS_PARAMS, Layout.PP_SIZE; lia].
unfold rtmb_slice, IMG. eapply Layout.pp_read_has_params; eassumption.
Qed.
Lemma rtmb_pp_params_struct : forall H mem pp, rtmb_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_PARAMS_STRUCT) 4 (Z.b2z pst).
Proof.
intros H mem pp B. apply (rtmb_pp_field H mem pp); [exact B | | unfold Layout.OFF_PARAMS_STRUCT; lia | unfold Layout.OFF_PARAMS_STRUCT, Layout.PP_SIZE; lia].
unfold rtmb_slice, IMG. eapply Layout.pp_read_params_struct; eassumption.
Qed.
Lemma rtmb_pp_n_ent : forall H mem pp, rtmb_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_N_ENT) 4 (Z.of_nat (length es)).
Proof.
intros H mem pp B. apply (rtmb_pp_field H mem pp); [exact B | | unfold Layout.OFF_N_ENT; lia | unfold Layout.OFF_N_ENT, Layout.PP_SIZE; lia].
unfold rtmb_slice, IMG. eapply Layout.pp_read_n_ent; eassumption.
Qed.
Lemma rtmb_pp_corrupt : forall H mem pp, rtmb_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_CORRUPT) 4 (Z.b2z corr).
Proof.
intros H mem pp B. apply (rtmb_pp_field H mem pp); [exact B | | unfold Layout.OFF_CORRUPT; lia | unfold Layout.OFF_CORRUPT, Layout.PP_SIZE; lia].
unfold rtmb_slice, IMG. eapply Layout.pp_read_corrupt; eassumption.
Qed.
Lemma rtmb_pp_ent : forall H mem pp i, rtmb_bytes H mem pp IMG -> (i < length es)%nat ->
rtmb_bytes H mem (pp + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i)) (Layout.ent_mem (nth i es (Model.Ent 0 0 []))).
Proof.
intros H mem pp i B Hi. pose proof rtmb_pp_len_img as L.
replace (pp + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i))
with (pp + Z.of_nat (Z.to_nat (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i)))
by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
pose proof (Layout.pp_read_ent b isp hasp pst es corr) as Er.
repeat lazymatch type of Er with
| Z.of_nat (length b) <= _ -> _ => specialize (Er Hb)
| (length es <= 32)%nat -> _ => specialize (Er He)
| Forall _ es -> _ => specialize (Er Hs) end.
rewrite <- (Er i Hi).
apply (rtmb_bytes_slice H mem pp IMG (Z.to_nat (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i)) 104); [exact B|].
unfold Layout.OFF_ENT, Layout.ENT_SIZE, Layout.PP_SIZE in *. pose proof He. lia.
Qed.
Lemma rtmb_pp_buf : forall H mem pp k n, rtmb_bytes H mem pp IMG -> (k + n <= length b)%nat ->
rtmb_bytes H mem (pp + Z.of_nat k) (rtmb_slice b k n).
Proof.
intros H mem pp k n B Hk. pose proof rtmb_pp_len_img as L. unfold IMG in *.
assert (E : rtmb_slice b k n = rtmb_slice (Layout.pp_image b isp hasp pst es corr) k n).
{ unfold rtmb_slice, Layout.pp_image. rewrite skipn_app. replace (k - length b)%nat with 0%nat by lia.
  cbn [skipn]. rewrite firstn_app, length_skipn. replace (n - (length b - k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity. }
rewrite E. apply rtmb_bytes_slice; [exact B|].
rewrite <- (Nat2Z.id (length (Layout.pp_image b isp hasp pst es corr))), L.
unfold Layout.PP_SIZE, Layout.POD_BUF_MAX in *. lia.
Qed.
End pp.

(* Read-only data the code loads without a check or after one (the tables ints / floats / t / t.11 / s and closed_list
   in .rodata, vocab / odd_ch / param in .data.rel.ro, the jump table at 0x20f6c): the image's bytes, by the harness
   pre's arodata_okP (RtPgBase; rt_seg_pre carries it), as rtmb_bytes of the list l the segments hold there. *)
Lemma rtmb_ro_bytes : forall B RLO RHI H mem a (l : list byte),
arodata_okP segs RLO RHI B (aview segs H mem) ->
(forall i, 0 <= i < Z.of_nat (length l) -> in_roP segs RLO RHI (a + i) /\
 ~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4)) ->
(forall i, (i < length l)%nat -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i l (Z_to_bv 8 0))) ->
rtmb_bytes H mem a l.
Proof.
intros B RLO RHI H mem a l Hro Hin Hrom. apply rtmb_bytes_aview. intros i Hi.
destruct (Hin (Z.of_nat i) ltac:(lia)) as (H1 & H2 & H3). rewrite (Hro _ H1 H2 H3), (Hrom i Hi). reflexivity.
Qed.

(* ========================================== 3. calls ========================================== *)
Lemma rtmb_memset_bytes : forall H' mem' d c n,
(forall i, 0 <= i < Z.of_nat n -> aview segs H' mem' (d + i) = Some (c mod 256)) ->
rtmb_bytes H' mem' d (repeat (Z_to_bv 8 c) n).
Proof.
intros H' mem' d c n A. apply rtmb_bytes_aview. intros i Hi. rewrite rtmb_length_repeat in Hi.
rewrite rtmb_nth_repeat by exact Hi. rewrite rtmb_unsigned_byte. apply A. lia.
Qed.

Lemma rtmb_memcpy_bytes : forall H mem H' mem' x d l,
rtmb_bytes H mem x l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview segs H' mem' (d + i) = aview segs H mem (x + i)) ->
rtmb_bytes H' mem' d l.
Proof.
intros H mem H' mem' x d l B A. apply rtmb_bytes_aview. intros i Hi. rewrite A by lia.
exact (proj1 (rtmb_bytes_aview _ _ _ _) B i Hi).
Qed.

Lemma rtmb_hull_sub : forall (rd : reader) x n y k,
shadow_hull_vis rd x n -> x <= y -> y + k <= x + n -> 0 < k -> shadow_hull_vis rd y k.
Proof.
intros rd x n y k Hh Hxy Hyk Hk. unfold shadow_hull_vis, shadow_addr in *. intros s Hs. apply Hh.
assert (A1 : (SHADOW_OFF + x / 8) / 8 <= (SHADOW_OFF + y / 8) / 8)
by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (A2 : (SHADOW_OFF + (y + k - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8)
by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
lia.
Qed.

Section blk.
Variable B : asyms.
Lemma rtmb_blk_ra : forall ly S W mem md p m a n,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) a n).
Proof.
intros ly S W mem md p m a n HAR Hin Hpa Han. split.
- exact (range_addressable_of_block segs B (AR_laws_ok segs B) ly S W mem md p m a n HAR Hin Hpa Han).
- intros Hn. destruct (al_shadow _ _ (AR_laws_ok segs B) ly S W mem md p m HAR Hin) as [_ Hh].
  exact (rtmb_hull_sub _ p (req_size m) a n Hh Hpa Han Hn).
Qed.
(* The shadow byte of a block's partial last granule: m mod 8 (buf for bl' mod 8 <> 0; the input block). *)
Lemma rtmb_blk_last : forall ly S W mem md p m,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> 0 < m -> m mod 8 <> 0 ->
aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF p + m / 8) = Some (m mod 8).
Proof.
intros ly S W mem md p m HAR Hin Hm Hm8.
destruct (al_shadow _ _ (AR_laws_ok segs B) ly S W mem md p m HAR Hin) as [(_ & _ & Hc) _].
unfold req_size in Hc. replace (m =? 0) with false in Hc by (symmetry; apply Z.eqb_neq; lia).
pose proof (Z.div_mod m 8 ltac:(lia)) as Edm. pose proof (Z.mod_pos_bound m 8 ltac:(lia)) as Hb.
assert (Hq : m / 8 + 1 <= (m + 7) / 8) by (apply Z.div_le_lower_bound; lia).
assert (H0 : 0 <= m / 8) by (apply Z.div_pos; lia).
rewrite (Hc (m / 8) ltac:(lia)), Z.ltb_irrefl. reflexivity.
Qed.
End blk.

(* ======================================= 4. shadow checks ======================================= *)
Lemma rtmb_ra_cell : forall (rd : reader) K x,
range_addressable rd K x 1 -> exists s, rd (shadow_of_addr K x) = Some s /\ saddr_ok x s.
Proof. intros rd K x R. exact (R x ltac:(lia)). Qed.

Lemma rtmb_ra_slow : forall x s, saddr_ok x s -> s <> 0 -> 0 < s < 8 /\ x mod 8 < s.
Proof. intros x s [E|[H1 H2]] Hs; [lia|]. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

Lemma rtmb_ra_slow_bv : forall x s, saddr_ok x s -> s <> 0 ->
bv_lts (Z_to_bv 64 (x mod 8)) (Z_to_bv 64 s) = true.
Proof.
intros x s Hok Hs. destruct (rtmb_ra_slow x s Hok Hs) as [H1 H2]. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
rewrite YCbn.bv_lts_small by lia. apply Z.ltb_lt. exact H2.
Qed.

Lemma rtmb_ra_lb : forall s, 0 <= s < 128 -> v_lb (Z_to_bv 8 s) = Z_to_bv 64 s.
Proof.
intros s Hs. exact (YCbn.cellval_small true (Z_to_bv 8 s) s ltac:(rewrite rtmb_unsigned_byte; apply Z.mod_small; lia) Hs).
Qed.

Lemma rtmb_ra_gran_false : forall (rd : reader) K p n,
block_shadow rd K p n -> 0 < n < 8 -> ~ range_addressable rd K p 8.
Proof.
intros rd K p n (Hp & _ & Hc) Hn R. specialize (Hc 0 ltac:(split; [lia | apply Z.div_str_pos; lia])).
rewrite Z.add_0_r in Hc. rewrite (Z.div_small n 8) in Hc by lia. cbn [Z.ltb Z.compare] in Hc.
rewrite (Z.mod_small n 8) in Hc by lia.
destruct (R (p + 7) ltac:(lia)) as (s & Hs & Hok).
replace (shadow_of_addr K (p + 7)) with (shadow_of_addr K p) in Hs.
- rewrite Hc in Hs. injection Hs as <-. destruct Hok as [E|[Hm _]]; [lia|].
  rewrite Z.add_mod, Hp in Hm by lia. cbn in Hm. lia.
- unfold shadow_of_addr. f_equal.
  replace (p + 7) with (7 + (p / 8) * 8) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
  rewrite Z.div_add by lia. cbn. lia.
Qed.

(* A one-byte region (no write window) at the address held by atom k, holding the byte s: the input's shadow cell
   (the seven `beqz t,+8; j L` input reads), or any other read-only byte. *)
Lemma rtmb_cell_region : forall E H mem (k : nat) sa s e,
bv_unsigned (ew E k) = sa -> aview segs H mem sa = Some s -> sv_denot E e = Z_to_bv 64 s ->
0 <= sa -> sa < 2 ^ 64 ->
region_ok segs E (mrestrict H mem) (YP09.mkRegion (Some k) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 e)]).
Proof.
intros E H mem k sa s e Hk A He H0 H1. destruct (rtmb_aview_val1 _ _ _ _ A) as [V R].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hk. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. apply (chunk_ok_val segs E _ sa 0 1 e s He); [cbn; lia | lia |].
rewrite Z.add_0_r. exact V.
Qed.

(* A region without a write window at the address held by atom k, with chunks cs. *)
Lemma rtmb_ro_region : forall E H mem (k : nat) b lo hi cs,
bv_unsigned (ew E k) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
Forall (YP09.chunk_ok segs E (mrestrict H mem) b) cs ->
region_ok segs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi 0 0 cs).
Proof.
intros E H mem k b lo hi cs Hk H0 H1 C. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hk. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact C].
Qed.

(* The same with the write window [wlo, whi), whose bytes are present (a block, a frame, the stack). *)
Lemma rtmb_rw_region : forall E H mem (k : nat) b lo hi wlo whi cs,
bv_unsigned (ew E k) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
(forall o, wlo <= o < whi -> apresent H mem (b + o)) ->
Forall (YP09.chunk_ok segs E (mrestrict H mem) b) cs ->
region_ok segs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi wlo whi cs).
Proof.
intros E H mem k b lo hi wlo whi cs Hk H0 H1 P C. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hk. split; [lia|]. split; [lia|]. split; [|exact C].
intros o Ho. apply (apresent_writable segs). apply P. exact Ho.
Qed.

Lemma rtmb_in_ra : forall (rd : reader) K src left c,
range_addressable rd K src left -> 0 <= c < left -> range_addressable rd K (src + c) 1.
Proof. intros rd K src left c R Hc. eapply range_addressable_sub; [exact R | lia | lia]. Qed.

(* An n-byte access at x inside one granule (x mod 8 + n <= 8), its bytes addressable: the shadow byte s of x's
   granule is 0, or 0 < s < 8 with the access's last offset x mod 8 + n - 1 below s, so the `bnez` check's slow block
   `andi u,x,7; addi u,u,n-1; blt u,t,back` returns (floats[20], closed_list[2], r[k]; image B has no asked[i] check). *)
Lemma rtmb_ra_cell_n : forall (rd : reader) K x n,
range_addressable rd K x n -> 0 < n -> x mod 8 + n <= 8 ->
exists s, rd (shadow_of_addr K x) = Some s /\ (s = 0 \/ (0 < s < 8 /\ x mod 8 + n - 1 < s)).
Proof.
intros rd K x n R Hn Hg. destruct (R (x + n - 1) ltac:(lia)) as (s & Hs & Hok).
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hm.
assert (Ey : x + n - 1 = (x mod 8 + n - 1) + (x / 8) * 8) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
assert (Ed : (x + n - 1) / 8 = x / 8).
{ rewrite Ey, Z.div_add by lia. rewrite Z.div_small by lia. lia. }
assert (Em : (x + n - 1) mod 8 = x mod 8 + n - 1).
{ rewrite Ey, Z.mod_add by lia. apply Z.mod_small. lia. }
exists s. split.
- unfold shadow_of_addr in *. rewrite <- Ed. exact Hs.
- destruct Hok as [E|[H1 H2]]; [left; exact E | right; rewrite Em in H1; lia].
Qed.

(* the slow block's `blt u,t` for that access, as the engine's branch condition *)
Lemma rtmb_ra_slow_n_bv : forall x n s, 0 < n -> x mod 8 + n <= 8 -> 0 < s < 8 -> x mod 8 + n - 1 < s ->
bv_lts (Z_to_bv 64 (x mod 8 + (n - 1))) (Z_to_bv 64 s) = true.
Proof.
intros x n s Hn Hg Hs Hl. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
rewrite YCbn.bv_lts_small by lia. apply Z.ltb_lt. lia.
Qed.

(* a 4-byte access at an 8-aligned address (floats[20] at 0x21190, closed_list[2] at 0x21528: 4 usable bytes) *)
Lemma rtmb_ra_cell4 : forall (rd : reader) K a,
range_addressable rd K a 4 -> a mod 8 = 0 ->
exists s, rd (shadow_of_addr K a) = Some s /\ (s = 0 \/ 3 < s < 8).
Proof.
intros rd K a R Ha. destruct (rtmb_ra_cell_n rd K a 4 R ltac:(lia) ltac:(lia)) as (s & Hs & Hc).
exists s. split; [exact Hs|]. lia.
Qed.

(* saddr_ok at an 8-aligned address: the byte is 0 or strictly between 0 and 8 *)
Lemma rtmb_sok_range : forall p s, p mod 8 = 0 -> saddr_ok p s -> 0 <= s <= 7.
Proof. intros p s Hp [->|[H1 H2]]; [lia|]. rewrite Hp in H1. lia. Qed.
Lemma rtmb_sok_pos : forall p s, p mod 8 = 0 -> saddr_ok p s -> s <> 0 -> 0 < s.
Proof. intros p s Hp [->|[H1 H2]] Hs; [lia|]. rewrite Hp in H1. lia. Qed.

(* ================================== 5. the stack's zero shadow ================================== *)
Section stk.
Variable B : asyms.
Lemma rtmb_stk_ra : forall ly S W mem md a n h,
AR segs B ly S W mem md -> ly_stk_lo ly <= a -> a + n <= h -> h <= ly_stk_hi ly -> h mod 8 = 0 ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n h HAR Hlo Hah Hh H8.
assert (Hin : In (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (zero_shadow_ranges B ly)) by (left; reflexivity).
pose proof (al_zshadow _ _ (AR_laws_ok segs B) ly S W mem md _ HAR Hin) as Z0. cbn [fst snd] in Z0.
destruct HAR as (HM & _).
destruct (zshadow_range_facts B ly S _ _ HM Hin) as (L8 & L0 & _). cbn [fst snd] in L8, L0.
set (lo := ly_stk_lo ly) in *. set (hi := ly_stk_hi ly) in *.
intros x Hx. exists 0. split; [|left; reflexivity].
assert (Elo : lo = 8 * (lo / 8)) by (pose proof (Z.div_mod lo 8 ltac:(lia)); lia).
assert (Eh : h = 8 * (h / 8)) by (pose proof (Z.div_mod h 8 ltac:(lia)); lia).
assert (Ei : shadow_of_addr SHADOW_OFF lo + (x - lo) / 8 = shadow_of_addr SHADOW_OFF x).
{ unfold shadow_of_addr. replace (x - lo) with (x + - (lo / 8) * 8) by lia.
  rewrite Z.div_add by lia. rewrite Elo at 1. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
rewrite <- Ei. apply Z0. split; [apply Z.div_pos; lia|].
assert ((x - lo) / 8 < (h - lo) / 8).
{ replace (h - lo) with ((h / 8 - lo / 8) * 8) by lia. rewrite Z.div_mul by lia.
  apply Z.div_lt_upper_bound; lia. }
assert ((h - lo) / 8 <= (hi - lo) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* The real-frame cells image B shadow-checks (hi_rz: [R+0x198, R+0x1a8)): parts[1]'s store8 check 0x81674 at R+0x1a0
   and pod_nearest's out cell at R+0x198 (its store8 check in pod_nearest). R + 0x220 <= h: the real frame lies below
   the entry sp (`addi sp,sp,-0x220` 0x8076c). *)
Lemma rtmb_B_rz : forall ly S W mem md R h,
AR segs B ly S W mem md -> ly_stk_lo ly <= R -> R + 0x220 <= h -> h <= ly_stk_hi ly -> h mod 8 = 0 ->
Forall (fun z => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (R + fst z) (snd z)) (hi_rz rate_himg_B).
Proof.
intros ly S W mem md R h HAR Hlo Hh Hhi H8. change (hi_rz rate_himg_B) with [(0x198, 16)]. constructor; [|constructor].
cbn [fst snd]. apply (rtmb_stk_ra ly S W mem md _ _ h HAR); lia.
Qed.
End stk.

(* ================================ 6. the frame for locals (image B) ================================
   The class-4 frame F (frame_alloc_4(704) 0x807dc; 1024 bytes, 128 shadow bytes): the frame description at .rodata
   0x113f3 reads "7 32 96 7 t.i.i.i 160 24 8 ch.i.i.i 224 4 7 r.i.i.i 240 104 3 e.i 384 104 5 e42.i 528 104 5 e62.i
   672 4 6 hz:248". e42 is the Int-7 pod of pod.h:413, e62 the count loop's pod of pod.h:426 (pod_write_ent takes each
   e by address: 0x81054 e, 0x82404 e42, 0x82108 e62). asked[] is not in F (section 7). *)
Definition RTMB_T : Z := 0x20.
Definition RTMB_CH : Z := 0xa0.
Definition RTMB_R : Z := 0xe0.
Definition RTMB_E : Z := 0xf0.
Definition RTMB_E42 : Z := 0x180.
Definition RTMB_E62 : Z := 0x210.
Definition RTMB_HZ : Z := 0x2a0.

(* The 88 shadow bytes of F the prologue writes, in a scope state: t (granules 0x04-0x0f), ch (0x14-0x16), e
   (0x1e-0x2a), e42 (0x30-0x3c), e62 (0x42-0x4e) are 0x00 in scope; r (0x1c) and hz (0x54) are 0x04 (4 bytes usable);
   out of scope 0xf8; the guards 0xf1 (0x00-0x03), 0xf2 (0x10-0x13, 0x17-0x1b, 0x1d, 0x2b-0x2f, 0x3d-0x41, 0x4f-0x53),
   0xf3 (0x55-0x57). Measured on the prologue's 88 stores 0x80850-0x809b0 (each `sb` off s3 = shadow_addr F with a3 =
   0xf1, a0 = 0xf8, a1 = 0xf2, a2 = 0xf3). Shadow bytes 0x58-0x7f of the frame are not written there and no access
   reaches F + 704 .. F + 1024. *)
Definition rtmb_sh (t ch r e e42 e62 hz : bool) : list Z :=
repeat 0xf1 4 ++ repeat (if t then 0 else 0xf8) 12 ++ repeat 0xf2 4 ++ repeat (if ch then 0 else 0xf8) 3 ++
repeat 0xf2 5 ++ [if r then 4 else 0xf8] ++ [0xf2] ++ repeat (if e then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++
repeat (if e42 then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++ repeat (if e62 then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++
[if hz then 4 else 0xf8] ++ repeat 0xf3 3.

Lemma rtmb_sh_len : forall t ch r e e42 e62 hz, length (rtmb_sh t ch r e e42 e62 hz) = 88%nat.
Proof. intros [] [] [] [] [] [] []; reflexivity. Qed.
(* P0 (C1, C2, C3, J83014) and PB (C4 .. C7: hz in scope, hz := 0x04 at 0x82a60) as image B's record holds them *)
Lemma rtmb_sh_P0 : rtmb_sh false false false false false false false = hi_shA rate_himg_B.
Proof. vm_compute. reflexivity. Qed.
Lemma rtmb_sh_PB : rtmb_sh false false false false false false true = hi_shB rate_himg_B.
Proof. vm_compute. reflexivity. Qed.
Lemma rtmb_sh_bytes : forall t ch r e e42 e62 hz, Forall (fun v => 0 <= v < 256) (rtmb_sh t ch r e e42 e62 hz).
Proof.
intros t ch r e e42 e62 hz. apply Forall_forall. intros v Hv.
assert (Hb : forallb (fun v => (0 <=? v) && (v <? 256)) (rtmb_sh t ch r e e42 e62 hz) = true)
  by (destruct t, ch, r, e, e42, e62, hz; vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb v Hv). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* entries j .. j+k-1 of pat set to v *)
Definition rtmb_setn (pat : list Z) (j k : nat) (v : Z) : list Z :=
map (fun i => if (j <=? i)%nat && (i <? j + k)%nat then v else nth i pat 0) (seq 0 (length pat)).

Lemma rtmb_setn_len : forall pat j k v, length (rtmb_setn pat j k v) = length pat.
Proof. intros. unfold rtmb_setn. rewrite length_map, length_seq. reflexivity. Qed.

Lemma rtmb_nth_setn : forall pat j k v i, (i < length pat)%nat ->
nth i (rtmb_setn pat j k v) 0 = if (j <=? i)%nat && (i <? j + k)%nat then v else nth i pat 0.
Proof.
intros pat j k v i Hi. unfold rtmb_setn.
set (f := fun i0 : nat => if (j <=? i0)%nat && (i0 <? j + k)%nat then v else nth i0 pat 0).
rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

(* The scope-store sites, as patterns (store groups measured on image B's code, each `sb` off s3 = shadow_addr F with
   the value set just before): e in 0x80ff4-0x81024 (pod.h:403) / out 0x81064-0x81098 (pod.h:406); e62 in
   0x813a4-0x813d4 (pod.h:426, each count turn) / out 0x8217c-0x821b4 and 0x82488-0x824bc (pod.h:433); t in
   0x81460-0x8148c and 0x814d0-0x814fc (pod.h:233); ch in 0x8150c-0x81514 and 0x81dbc-0x81dc4 (pod.h:235); r in
   0x81534 (4, pod.h:238) / out 0x81608 (s8 = -8, pod.h:246);
   t and ch out 0x8172c-0x81764 (pod.h:262); e42 in 0x82398-0x823c8 (pod.h:413) / out 0x82438-0x8246c (pod.h:420);
   hz in 0x82a60 (4, fuzz_rate.c:248) / out 0x83008 (fuzz_rate.c:284). *)
Lemma rtmb_sh_t_in : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 4 12 0 = rtmb_sh true ch r e e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_t_out : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 4 12 0xf8 = rtmb_sh false ch r e e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_ch_in : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 20 3 0 = rtmb_sh t true r e e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_ch_out : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 20 3 0xf8 = rtmb_sh t false r e e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_r_in : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 28 1 4 = rtmb_sh t ch true e e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_r_out : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 28 1 0xf8 = rtmb_sh t ch false e e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_e_in : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 30 13 0 = rtmb_sh t ch r true e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_e_out : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 30 13 0xf8 = rtmb_sh t ch r false e42 e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_e42_in : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 48 13 0 = rtmb_sh t ch r e true e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_e42_out : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 48 13 0xf8 = rtmb_sh t ch r e false e62 hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_e62_in : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 66 13 0 = rtmb_sh t ch r e e42 true hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_e62_out : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 66 13 0xf8 = rtmb_sh t ch r e e42 false hz.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_hz_in : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 84 1 4 = rtmb_sh t ch r e e42 e62 true.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rtmb_sh_hz_out : forall t ch r e e42 e62 hz,
rtmb_setn (rtmb_sh t ch r e e42 e62 hz) 84 1 0xf8 = rtmb_sh t ch r e e42 e62 false.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.

Lemma rtmb_fsh_kept : forall H mem H' mem' F pat,
rt_fsh segs H mem F pat ->
(forall i, 0 <= i < Z.of_nat (length pat) ->
 aview segs H' mem' (shadow_addr F + i) = aview segs H mem (shadow_addr F + i)) ->
rt_fsh segs H' mem' F pat.
Proof. intros H mem H' mem' F pat P K i Hi. rewrite K by exact Hi. exact (P i Hi). Qed.

Lemma rtmb_fsh_set : forall H mem H' mem' F pat j k v,
rt_fsh segs H mem F pat ->
(forall i, Z.of_nat j <= i < Z.of_nat (j + k) -> aview segs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, 0 <= i < Z.of_nat (length pat) -> ~ (Z.of_nat j <= i < Z.of_nat (j + k)) ->
 aview segs H' mem' (shadow_addr F + i) = aview segs H mem (shadow_addr F + i)) ->
rt_fsh segs H' mem' F (rtmb_setn pat j k v).
Proof.
intros H mem H' mem' F pat j k v P Sv K i Hi. rewrite rtmb_setn_len in Hi.
rewrite rtmb_nth_setn by lia.
destruct ((j <=? Z.to_nat i)%nat && (Z.to_nat i <? j + k)%nat) eqn:Ein.
- apply andb_prop in Ein as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. apply Sv. lia.
- assert (Hn : ~ (Z.of_nat j <= i < Z.of_nat (j + k))).
  { intros [E1 E2]. apply andb_false_iff in Ein as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia. }
  rewrite (K i Hi Hn). exact (P i Hi).
Qed.

Lemma rtmb_fsh_ra : forall H mem F pat o n,
rt_fsh segs H mem F pat -> F mod 8 = 0 -> 0 <= o -> o + n <= 8 * Z.of_nat (length pat) ->
(forall i, o <= i < o + n -> saddr_ok i (nth (Z.to_nat (i / 8)) pat 0)) ->
range_addressable (aview segs H mem) SHADOW_OFF (F + o) n.
Proof.
intros H mem F pat o n P HF Ho Hn Hok x Hx. set (i := x - F).
assert (Ex : x = F + i) by (subst i; lia).
assert (Esh : shadow_of_addr SHADOW_OFF x = shadow_addr F + i / 8).
{ unfold shadow_of_addr, shadow_addr. rewrite Ex. rewrite (Z.div_mod F 8) at 1 by lia. rewrite HF, Z.add_0_r.
  rewrite <- Z.add_assoc, (Z.add_comm (8 * (F / 8))), Z.mul_comm, Z.div_add by lia. lia. }
exists (nth (Z.to_nat (i / 8)) pat 0). split.
- rewrite Esh. apply P. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
- assert (Hm : x mod 8 = i mod 8).
  { rewrite Ex, Z.add_mod, HF by lia. rewrite Z.add_0_l, Z.mod_mod by lia. reflexivity. }
  destruct (Hok i ltac:(lia)) as [E|[E1 E2]]; [left; exact E | right; rewrite Hm; split; assumption].
Qed.

Lemma rtmb_nth_range : forall pat (a len : nat) (z : Z),
forallb (fun g => nth g pat 0 =? z) (seq a len) = true -> forall g, (a <= g < a + len)%nat -> nth g pat 0 = z.
Proof.
intros pat a len z H g Hg. rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_seq. lia.
Qed.

(* An object of len granules from granule g0, every granule's shadow byte v: 0 (any bytes of it usable), or a single
   granule with 0 < v < 8 (its first v bytes usable). *)
Lemma rtmb_fsh_ra_obj : forall H mem F pat (g0 len : nat) v o n,
rt_fsh segs H mem F pat -> F mod 8 = 0 -> (g0 + len <= length pat)%nat ->
(forall g, (g0 <= g < g0 + len)%nat -> nth g pat 0 = v) ->
0 <= o -> o + n <= 8 * Z.of_nat len -> (v = 0 \/ (len = 1%nat /\ 0 < v < 8 /\ o + n <= v)) ->
range_addressable (aview segs H mem) SHADOW_OFF (F + 8 * Z.of_nat g0 + o) n.
Proof.
intros H mem F pat g0 len v o n P HF Hl Hv Ho Hn Hc.
replace (F + 8 * Z.of_nat g0 + o) with (F + (8 * Z.of_nat g0 + o)) by lia.
apply (rtmb_fsh_ra H mem F pat); [exact P | exact HF | lia | lia |].
intros i Hi.
assert (Hg : (g0 <= Z.to_nat (i / 8) < g0 + len)%nat).
{ split.
  - apply Nat2Z.inj_le. rewrite Z2Nat.id by (apply Z.div_pos; lia). apply Z.div_le_lower_bound; lia.
  - apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). rewrite Nat2Z.inj_add.
    apply Z.div_lt_upper_bound; lia. }
rewrite (Hv _ Hg).
destruct Hc as [-> | (Hl1 & Hv8 & Hon)]; [left; reflexivity|].
subst len. right.
assert (Ei : i / 8 = Z.of_nat g0).
{ assert (Eg : Z.to_nat (i / 8) = g0) by lia. rewrite <- Eg. rewrite Z2Nat.id by (apply Z.div_pos; lia). reflexivity. }
pose proof (Z.div_mod i 8 ltac:(lia)) as Edm. lia.
Qed.

(* The checks and the calls on the frame objects: each in-scope object's bytes are addressable. F mod 8 = 0: YG0d
   AR_frames_law gives F mod 32 = 0. e, e42 and e62 are the q of pod_write_ent's three calls (0x81054, 0x82404,
   0x82108): its 104 bytes are addressable while the object is in scope. *)
Lemma rtmb_B_ra_t : forall H mem F ch r e e42 e62 hz o n,
rt_fsh segs H mem F (rtmb_sh true ch r e e42 e62 hz) -> F mod 8 = 0 -> 0 <= o -> o + n <= 96 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RTMB_T + o) n.
Proof.
intros H mem F ch r e e42 e62 hz o n P HF Ho Hn. unfold RTMB_T. change 0x20 with (8 * Z.of_nat 4).
apply (rtmb_fsh_ra_obj H mem F _ 4 12 0 o n P HF); [rewrite rtmb_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rtmb_nth_range _ 4 12); [|lia]. destruct ch, r, e, e42, e62, hz; vm_compute; reflexivity.
Qed.

Lemma rtmb_B_ra_ch : forall H mem F t r e e42 e62 hz o n,
rt_fsh segs H mem F (rtmb_sh t true r e e42 e62 hz) -> F mod 8 = 0 -> 0 <= o -> o + n <= 24 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RTMB_CH + o) n.
Proof.
intros H mem F t r e e42 e62 hz o n P HF Ho Hn. unfold RTMB_CH. change 0xa0 with (8 * Z.of_nat 20).
apply (rtmb_fsh_ra_obj H mem F _ 20 3 0 o n P HF); [rewrite rtmb_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rtmb_nth_range _ 20 3); [|lia]. destruct t, r, e, e42, e62, hz; vm_compute; reflexivity.
Qed.

Lemma rtmb_B_ra_e : forall H mem F t ch r e42 e62 hz o n,
rt_fsh segs H mem F (rtmb_sh t ch r true e42 e62 hz) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RTMB_E + o) n.
Proof.
intros H mem F t ch r e42 e62 hz o n P HF Ho Hn. unfold RTMB_E. change 0xf0 with (8 * Z.of_nat 30).
apply (rtmb_fsh_ra_obj H mem F _ 30 13 0 o n P HF); [rewrite rtmb_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rtmb_nth_range _ 30 13); [|lia]. destruct t, ch, r, e42, e62, hz; vm_compute; reflexivity.
Qed.

Lemma rtmb_B_ra_e42 : forall H mem F t ch r e e62 hz o n,
rt_fsh segs H mem F (rtmb_sh t ch r e true e62 hz) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RTMB_E42 + o) n.
Proof.
intros H mem F t ch r e e62 hz o n P HF Ho Hn. unfold RTMB_E42. change 0x180 with (8 * Z.of_nat 48).
apply (rtmb_fsh_ra_obj H mem F _ 48 13 0 o n P HF); [rewrite rtmb_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rtmb_nth_range _ 48 13); [|lia]. destruct t, ch, r, e, e62, hz; vm_compute; reflexivity.
Qed.

Lemma rtmb_B_ra_e62 : forall H mem F t ch r e e42 hz o n,
rt_fsh segs H mem F (rtmb_sh t ch r e e42 true hz) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RTMB_E62 + o) n.
Proof.
intros H mem F t ch r e e42 hz o n P HF Ho Hn. unfold RTMB_E62. change 0x210 with (8 * Z.of_nat 66).
apply (rtmb_fsh_ra_obj H mem F _ 66 13 0 o n P HF); [rewrite rtmb_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rtmb_nth_range _ 66 13); [|lia]. destruct t, ch, r, e, e42, hz; vm_compute; reflexivity.
Qed.

(* r and hz: shadow byte 0x04, so each access passes on the check's slow path (its last offset in the granule < 4):
   r's two checks (pod.h:240 r[k] 0x81564, pod.h:244 r[k-1-i] 0x815b8); hz is the parse's out argument (a1 = F+0x2a0
   at the call 0x82a7c), whose 4 bytes the callee checks. *)
Lemma rtmb_B_ra_r : forall H mem F t ch e e42 e62 hz o n,
rt_fsh segs H mem F (rtmb_sh t ch true e e42 e62 hz) -> F mod 8 = 0 -> 0 <= o -> o + n <= 4 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RTMB_R + o) n.
Proof.
intros H mem F t ch e e42 e62 hz o n P HF Ho Hn. unfold RTMB_R. change 0xe0 with (8 * Z.of_nat 28).
apply (rtmb_fsh_ra_obj H mem F _ 28 1 4 o n P HF); [rewrite rtmb_sh_len; lia | | lia | lia | right; lia].
intros g Hg. apply (rtmb_nth_range _ 28 1); [|lia]. destruct t, ch, e, e42, e62, hz; vm_compute; reflexivity.
Qed.

Lemma rtmb_B_ra_hz : forall H mem F t ch r e e42 e62 o n,
rt_fsh segs H mem F (rtmb_sh t ch r e e42 e62 true) -> F mod 8 = 0 -> 0 <= o -> o + n <= 4 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RTMB_HZ + o) n.
Proof.
intros H mem F t ch r e e42 e62 o n P HF Ho Hn. unfold RTMB_HZ. change 0x2a0 with (8 * Z.of_nat 84).
apply (rtmb_fsh_ra_obj H mem F _ 84 1 4 o n P HF); [rewrite rtmb_sh_len; lia | | lia | lia | right; lia].
intros g Hg. apply (rtmb_nth_range _ 84 1); [|lia]. destruct t, ch, r, e, e42, e62; vm_compute; reflexivity.
Qed.

(* The frame-shadow region's chunks: one `CVal 1 (SLit v)` per shadow byte, from shadow_addr F. *)
Definition rtmb_fsh_cs (pat : list Z) : list YP09.chunk :=
map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i pat 0)))) (seq 0 (length pat)).

Lemma rtmb_fsh_chunks : forall E H mem F pat,
rt_fsh segs H mem F pat -> Forall (fun v => 0 <= v < 256) pat ->
Forall (YP09.chunk_ok segs E (mrestrict H mem) (shadow_addr F)) (rtmb_fsh_cs pat).
Proof.
intros E H mem F pat P R. apply Forall_forall. intros c Hc. unfold rtmb_fsh_cs in Hc.
apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
assert (Rv : 0 <= nth i pat 0 < 256) by (rewrite Forall_forall in R; apply R; apply nth_In; lia).
apply (chunk_ok_val segs E _ (shadow_addr F) (Z.of_nat i) 1 (SLit (nth i pat 0)) (nth i pat 0));
[reflexivity | cbn; lia | lia |].
apply (rtmb_aview_val1 H mem). rewrite (P (Z.of_nat i) ltac:(lia)), Nat2Z.id. reflexivity.
Qed.

Lemma rtmb_fsh_of_chunks : forall E H mem F pat,
Forall (YP09.chunk_ok segs E (mrestrict H mem) (shadow_addr F)) (rtmb_fsh_cs pat) ->
Forall (fun v => 0 <= v < 256) pat -> rt_fsh segs H mem F pat.
Proof.
intros E H mem F pat C R i Hi. rewrite Forall_forall in C.
assert (Hin : In (YP09.mkChunk (Z.of_nat (Z.to_nat i)) (CVal 1 (SLit (nth (Z.to_nat i) pat 0)))) (rtmb_fsh_cs pat)).
{ unfold rtmb_fsh_cs. apply in_map_iff. exists (Z.to_nat i). split; [reflexivity|]. apply in_seq. lia. }
pose proof (C _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite Z2Nat.id, Z.add_0_r in Hb2 by lia.
injection Hb1 as <-.
assert (Rv : 0 <= nth (Z.to_nat i) pat 0 < 256) by (rewrite Forall_forall in R; apply R; apply nth_In; lia).
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r, unsigned_lit_small by lia.
rewrite rtmb_unsigned_byte. apply Z.mod_small. exact Rv.
Qed.

(* ================================== 7. the real frame's cells ================================== *)
Definition rtmb_slots (H : word -> bool) (mem : word -> option byte) (R : Z) (l : list (Z * Z)) : Prop :=
Forall (fun c => val_mem segs (mrestrict H mem) (R + fst c) 8 (snd c mod 2 ^ 64)) l.

Lemma rtmb_slots_kept : forall H mem H' mem' R l,
rtmb_slots H mem R l ->
(forall c, In c l -> forall i, 0 <= i < 8 -> aview segs H' mem' (R + fst c + i) = aview segs H mem (R + fst c + i)) ->
rtmb_slots H' mem' R l.
Proof.
intros H mem H' mem' R l P K. unfold rtmb_slots in *. rewrite Forall_forall in *. intros c Hc k Hk.
rewrite (mbyte_of_aview segs H H' mem mem') by (apply K; [exact Hc | lia]). exact (P c Hc k Hk).
Qed.

Lemma rtmb_slots_chunk : forall E H mem R l o v e,
rtmb_slots H mem R l -> In (o, v) l -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
YP09.chunk_ok segs E (mrestrict H mem) R (YP09.mkChunk o (CVal 8 e)).
Proof.
intros E H mem R l o v e P Hin He Hv. unfold rtmb_slots in P. rewrite Forall_forall in P.
pose proof (P _ Hin) as V. cbn [fst snd] in V. rewrite Z.mod_small in V by lia.
apply (chunk_ok_val segs E _ R o 8 e v He); [cbn; lia | lia | exact V].
Qed.

(* RtPgBase's cut facts (rt_at / rt_cut) carried across a step, a store or a call: a register fact needs the register
   unchanged, a cell fact its 8 bytes unchanged. *)
Definition rtmb_keeps (H : word -> bool) (mem : word -> option byte) (H' : word -> bool) (mem' : word -> option byte)
(regs regs' : bvmap 5 word) (e : rt_renv) (l : rt_loc) : Prop :=
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall i, 0 <= i < 8 -> aview segs H' mem' (rt_xv e b + o + i) = aview segs H mem (rt_xv e b + o + i)
end.

Lemma rtmb_at_kept : forall H mem H' mem' regs regs' e l v,
rt_at segs H mem regs e l v -> rtmb_keeps H mem H' mem' regs regs' e l -> rt_at segs H' mem' regs' e l v.
Proof.
intros H mem H' mem' regs regs' e [r|b o] v A K; cbn [rt_at rtmb_keeps] in *.
- rewrite K. exact A.
- intros k Hk. rewrite (mbyte_of_aview segs H H' mem mem') by (apply K; lia). exact (A k Hk).
Qed.

Lemma rtmb_cut_kept : forall H mem H' mem' regs regs' e L,
rt_cut segs H mem regs e L -> (forall f, In f L -> rtmb_keeps H mem H' mem' regs regs' e (fst f)) ->
rt_cut segs H' mem' regs' e L.
Proof.
intros H mem H' mem' regs regs' e L C K. unfold rt_cut in *. rewrite Forall_forall in *. intros f Hf.
exact (rtmb_at_kept _ _ _ _ _ _ _ _ _ (C f Hf) (K f Hf)).
Qed.

(* The same over a list of (location, value) facts (a cut fact list of the walk's sub-cut states unfolds to this). *)
Lemma rtmb_atl_kept : forall H mem H' mem' regs regs' e (L : list (rt_loc * Z)),
Forall (fun f => rt_at segs H mem regs e (fst f) (snd f)) L ->
(forall f, In f L -> rtmb_keeps H mem H' mem' regs regs' e (fst f)) ->
Forall (fun f => rt_at segs H' mem' regs' e (fst f) (snd f)) L.
Proof.
intros H mem H' mem' regs regs' e L C K. rewrite Forall_forall in *. intros f Hf.
exact (rtmb_at_kept _ _ _ _ _ _ _ _ _ (C f Hf) (K f Hf)).
Qed.

(* rtmb_keeps from what a step changed: Wr is the set of bytes it may write (a store: [a, a + n)); a register fact
   needs its register unchanged, a cell fact its 8 bytes outside Wr. *)
Lemma rtmb_keeps_of : forall (Wr : Z -> Prop) H mem H' mem' regs regs' e l,
(forall x, ~ Wr x -> aview segs H' mem' x = aview segs H mem x) ->
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall i, 0 <= i < 8 -> ~ Wr (rt_xv e b + o + i)
end ->
rtmb_keeps H mem H' mem' regs regs' e l.
Proof. intros Wr H mem H' mem' regs regs' e [r|b o] K L; cbn [rtmb_keeps]; [exact L|]. intros i Hi. apply K, L, Hi. Qed.

(* rtmb_keeps across a call, from its post's memory clause (every byte outside the callee's stack [sp - T, sp) and
   outside E kept: RtPgCSpec rt_post, YG0d's intrinsic and allocator posts) and aregs_preserved. *)
Lemma rtmb_keeps_call : forall (E : Z -> Prop) sp T H mem H' mem' regs regs' e l,
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - T <= a < sp) -> ~ E a -> aview segs H' mem' a = aview segs H mem a) ->
aregs_preserved regs regs' ->
match l with
| LReg r => acallee_saved r
| LCell b o => forall i, 0 <= i < 8 ->
  0 <= rt_xv e b + o + i < 2 ^ 64 /\ ~ (sp - T <= rt_xv e b + o + i < sp) /\ ~ E (rt_xv e b + o + i)
end ->
rtmb_keeps H mem H' mem' regs regs' e l.
Proof.
intros E sp T H mem H' mem' regs regs' e [r|b o] K P L; cbn [rtmb_keeps].
- exact (P r L).
- intros i Hi. destruct (L i Hi) as (L1 & L2 & L3). exact (K _ L1 L2 L3).
Qed.

(* asked[0] / asked[1] in the real-frame cells R+0x198 / R+0x19c (image B keeps them on the real stack, without a
   check): written by `sw a2,0x198(s1)` 0x82e30 and `sw a0,0x19c(s1)` 0x82e34, read back in the decide loop by
   `lw s7,0(s8)` 0x82e50 and `lw s11,0(s8)` 0x82f44 with s8 = R+0x198+4t. The same 8 bytes are pod_nearest's out cell
   (a0 = R+0x198 at 0x82dc0) and case 0's parts[0] (`sd a2,0x198(s1)` 0x81664), so a cut holds them as one 8-byte cell
   (rt_at (LCell XR 0x198)) or as two 4-byte cells; these two lemmas go between the forms. *)
Lemma rtmb_shiftr_mod_low : forall x n m p, 0 <= m -> 0 <= p -> m + p <= n ->
Z.shiftr (x mod 2 ^ n) m mod 2 ^ p = Z.shiftr x m mod 2 ^ p.
Proof.
intros x n m p Hm Hp Hn. apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i p) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma rtmb_lb_lo : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
le_byte (lo + 2 ^ 32 * hi) 8 k = le_byte lo 4 k.
Proof.
intros lo hi k Hl Hh Hk. unfold le_byte.
change (8 * Z.of_nat 8) with 64. change (8 * Z.of_nat 4) with 32.
assert (Hv : 0 <= lo + 2 ^ 32 * hi < 2 ^ 64).
{ first [lia | change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia]. }
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by exact Hv. rewrite (Z.mod_small lo (2 ^ 32)) by exact Hl.
change 256 with (2 ^ 8).
rewrite <- (rtmb_shiftr_mod_low (lo + 2 ^ 32 * hi) 32) by lia.
f_equal. f_equal. replace (lo + 2 ^ 32 * hi) with (lo + hi * 2 ^ 32) by ring.
rewrite Z.mod_add by lia. apply Z.mod_small. exact Hl.
Qed.

Lemma rtmb_lb_hi : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (4 <= k < 8)%nat ->
le_byte (lo + 2 ^ 32 * hi) 8 k = le_byte hi 4 (k - 4).
Proof.
intros lo hi k Hl Hh Hk. unfold le_byte.
change (8 * Z.of_nat 8) with 64. change (8 * Z.of_nat 4) with 32.
assert (Hv : 0 <= lo + 2 ^ 32 * hi < 2 ^ 64).
{ first [lia | change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia]. }
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by exact Hv. rewrite (Z.mod_small hi (2 ^ 32)) by exact Hh.
replace (8 * Z.of_nat k) with (32 + 8 * Z.of_nat (k - 4)) by lia.
rewrite <- Z.shiftr_shiftr by lia. f_equal. f_equal.
rewrite Z.shiftr_div_pow2 by lia. replace (lo + 2 ^ 32 * hi) with (lo + hi * 2 ^ 32) by ring.
rewrite Z.div_add by lia. rewrite Z.div_small by exact Hl. lia.
Qed.

Lemma rtmb_ask_join : forall (M : word -> option byte) a v0 v1,
val_mem segs M a 4 (v0 mod 2 ^ 32) -> val_mem segs M (a + 4) 4 (v1 mod 2 ^ 32) ->
val_mem segs M a 8 (v0 mod 2 ^ 32 + 2 ^ 32 * (v1 mod 2 ^ 32)).
Proof.
intros M a v0 v1 V0 V1 k Hk.
pose proof (Z.mod_pos_bound v0 (2 ^ 32) ltac:(lia)) as B0. pose proof (Z.mod_pos_bound v1 (2 ^ 32) ltac:(lia)) as B1.
destruct (Nat.lt_ge_cases k 4) as [Hl|Hg].
- rewrite (V0 k Hl). f_equal. f_equal. exact (eq_sym (rtmb_lb_lo _ _ k B0 B1 Hl)).
- replace (a + Z.of_nat k) with (a + 4 + Z.of_nat (k - 4)) by lia.
  rewrite (V1 (k - 4)%nat ltac:(lia)). f_equal. f_equal. exact (eq_sym (rtmb_lb_hi _ _ k B0 B1 ltac:(lia))).
Qed.

Lemma rtmb_ask_split : forall (M : word -> option byte) a v0 v1,
val_mem segs M a 8 (v0 mod 2 ^ 32 + 2 ^ 32 * (v1 mod 2 ^ 32)) ->
val_mem segs M a 4 (v0 mod 2 ^ 32) /\ val_mem segs M (a + 4) 4 (v1 mod 2 ^ 32).
Proof.
intros M a v0 v1 V.
pose proof (Z.mod_pos_bound v0 (2 ^ 32) ltac:(lia)) as B0. pose proof (Z.mod_pos_bound v1 (2 ^ 32) ltac:(lia)) as B1.
split; intros k Hk.
- rewrite (V k ltac:(lia)). f_equal. f_equal. exact (rtmb_lb_lo _ _ k B0 B1 Hk).
- replace (a + 4 + Z.of_nat k) with (a + Z.of_nat (k + 4)) by lia.
  rewrite (V (k + 4)%nat ltac:(lia)). f_equal. f_equal.
  etransitivity; [exact (rtmb_lb_hi _ _ (k + 4) B0 B1 ltac:(lia)) |].
  replace (k + 4 - 4)%nat with k by lia. reflexivity.
Qed.

(* ========================= 9. the segment's start facts at the current memory =========================
   A cut inside a segment knows the start state's facts (rt_seg_pre, the input premises) and that every byte outside
   a write set Wr (rt_seg_post's kept clause: the callees' stack below R and the image's write ranges) is as at the
   start. These carry the input bytes, their shadow bytes, the shadow hull and rom_view to the current memory; the
   address facts after them show that the input's shadow bytes avoid each part of Wr. *)
Lemma rtmb_bytes_kept_wr : forall (Wr : Z -> Prop) H mem H' mem' a l,
rtmb_bytes H mem a l -> (forall x, ~ Wr x -> aview segs H' mem' x = aview segs H mem x) ->
(forall x, a <= x < a + Z.of_nat (length l) -> ~ Wr x) -> rtmb_bytes H' mem' a l.
Proof. intros Wr H mem H' mem' a l B K D. apply (rtmb_bytes_kept H mem); [exact B|]. intros x Hx. apply K, D, Hx. Qed.

Lemma rtmb_ra_kept : forall H mem H' mem' K a n,
range_addressable (aview segs H mem) K a n ->
(forall x, a <= x < a + n -> aview segs H' mem' (shadow_of_addr K x) = aview segs H mem (shadow_of_addr K x)) ->
range_addressable (aview segs H' mem') K a n.
Proof. intros H mem H' mem' K a n R E. exact (range_addressable_agree _ _ K a n E R). Qed.

Lemma rtmb_ra_kept_wr : forall (Wr : Z -> Prop) H mem H' mem' K a n,
range_addressable (aview segs H mem) K a n -> (forall x, ~ Wr x -> aview segs H' mem' x = aview segs H mem x) ->
(forall x, a <= x < a + n -> ~ Wr (shadow_of_addr K x)) -> range_addressable (aview segs H' mem') K a n.
Proof. intros Wr H mem H' mem' K a n R E D. apply (rtmb_ra_kept H mem); [exact R|]. intros x Hx. apply E, D, Hx. Qed.

Lemma rtmb_hull_kept : forall H mem H' mem' x n,
shadow_hull_vis (aview segs H mem) x n ->
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
 aview segs H mem s <> None -> aview segs H' mem' s <> None) ->
shadow_hull_vis (aview segs H' mem') x n.
Proof. intros H mem H' mem' x n V P s Hs. exact (P s Hs (V s Hs)). Qed.

Lemma rtmb_rom_kept : forall (W W' : world segs) mem mem',
rom_view segs W mem -> (forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
rom_view segs W' mem'.
Proof. intros W W' mem mem' R K a Ha. rewrite K by exact Ha. exact (R a Ha). Qed.

Lemma rtmb_rom_kept_wr : forall (Wr : Z -> Prop) (W W' : world segs) mem mem',
rom_view segs W mem -> (forall a, ~ Wr a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall a, in_rom segs a -> ~ Wr a) -> rom_view segs W' mem'.
Proof. intros Wr W W' mem mem' R K D. apply (rtmb_rom_kept W W' mem mem' R). intros a Ha. apply K, D, Ha. Qed.

(* An addressable range's shadow bytes are not the frame's poisoned ones: at one state, a shadow byte that some
   addressable byte reads is 0 or below 8, and every byte of a pattern like P0 is 0xf1 .. 0xf8. *)
Lemma rtmb_ra_not_fsh : forall H mem F pat a n,
range_addressable (aview segs H mem) SHADOW_OFF a n -> rt_fsh segs H mem F pat -> Forall (fun v => 8 <= v) pat ->
forall x, a <= x < a + n ->
~ (shadow_addr F <= shadow_of_addr SHADOW_OFF x < shadow_addr F + Z.of_nat (length pat)).
Proof.
intros H mem F pat a n R P B x Hx Hin. destruct (R x Hx) as (s & Hs & Hok).
set (i := shadow_of_addr SHADOW_OFF x - shadow_addr F) in *.
pose proof (P i ltac:(subst i; lia)) as Pi.
replace (shadow_addr F + i) with (shadow_of_addr SHADOW_OFF x) in Pi by (subst i; lia).
rewrite Hs in Pi. injection Pi as Ei.
assert (Hb : 8 <= nth (Z.to_nat i) pat 0).
{ rewrite Forall_forall in B. apply B. apply nth_In. lia. }
destruct Hok as [E|[_ E]]; lia.
Qed.

End mem.

(* The shadow band: the shadow byte of an address below kHighMemEnd lies in [kLowMemEnd, kHighMemBeg), apart from
   the application ranges (in_app: blocks, frames for locals) and from everything at or above kHighMemBeg (the
   stack, the real frame's cells). P0's bytes are all >= 8 (rtmb_ra_not_fsh's premise). *)
Lemma rtmb_shadow_band : forall x, 0 <= x < kHighMemEnd ->
kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg. unfold kHighMemEnd in Hx.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.
Section band. Context {rc : YM05.RunCeil}.
Lemma rtmb_shadow_not_app : forall x lo len, 0 <= x < kHighMemEnd -> in_app lo len ->
~ (lo <= shadow_of_addr SHADOW_OFF x < lo + len).
Proof.
intros x lo len Hx Ha Hin. pose proof (rtmb_shadow_band x Hx) as Hb.
unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg in *. lia.
Qed.
End band.
Lemma rtmb_shadow_not_high : forall x lo, 0 <= x < kHighMemEnd -> kHighMemBeg <= lo ->
~ (lo <= shadow_of_addr SHADOW_OFF x).
Proof. intros x lo Hx Hl Hin. pose proof (rtmb_shadow_band x Hx). lia. Qed.
Lemma rtmb_sh_P0_big : Forall (fun v => 8 <= v) (hi_shA rate_himg_B).
Proof. rewrite <- rtmb_sh_P0. cbv [rtmb_sh repeat app]. repeat constructor; lia. Qed.

(* ============================ 8. risk 2 at its concrete site, 0x809d8 (E01, header byte 0) ============================
   The code, read from image B's loaded segments: 0x809d0 srli a1,s2,3; 0x809d4 add a1,a1,s4; 0x809d8 lb a1,0(a1);
   0x809dc beqz a1,+8; 0x809e0 j 0x830d4; 0x809e4 lbu a4,0(s2); and 0x830d4 andi a2,s2,7; 0x830d8 bge a2,a1,+8;
   0x830dc j 0x809e4; 0x830e0 mv a0,s2 (the report call follows). s2 is the input pointer p, s4 the shadow offset. The
   trap guard before it (0x809c0 addi a0,s2,1; li a1,1; bltu a1,a0,+8; j 0x83098) is its own step.
   rtmb_B_tok_none: the engine's slow-block recognizer (YCbn.slow_block) fails at the `beqz`'s fall-through 0x809e0
   (a `j`, decoded, not an `andi`), so tok_branch takes its None arm (shadow 0 over the whole granule); rtmb_B_slow_ok:
   the out-of-line block 0x830d4 itself has the shape the recognizer accepts. rtmb_B_809d8_gran: for an input of
   1 .. 7 bytes that obligation is false at header byte 0; rtmb_B_809d8_cell: the shadow cell the route loads instead,
   and why its report arm is dead. Five more sites have this shape (0x80a0c, 0x80a80, 0x80b18, 0x80b68, 0x81360: the
   `bge; j back` slow block) and differ in registers and in the cursor; 0x80fcc's slow block is `blt; j report; j back`
   (rtmb_B_80fcc_step below). *)
Definition rtmb_B_tbl809d8 : ctable := build_table rsegs 0x809d0 6 (build_table rsegs 0x830d4 4 TEmpty).
Lemma rtmb_B_tbl809d8_ok : table_ok rsegs rtmb_B_tbl809d8.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

Lemma rtmb_B_tok_none : forall t, YCbn.slow_block rtmb_B_tbl809d8 0x809e0 0x809e4 t = None.
Proof. intros t. vm_compute. reflexivity. Qed.
Lemma rtmb_B_tok_arm :
match YCbn.dec rtmb_B_tbl809d8 0x809e0 with
| Some i => match YCbn.as_andi i with Some _ => false | None => true end
| None => false end = true /\
YCbn.decp rtmb_B_tbl809d8 YCbn.as_j 0x809e0 = Some (0x830d4 - 0x809e0) /\
match YCbn.decp rtmb_B_tbl809d8 YCbn.as_branch 0x809dc with
| Some (c, r1, r2, off) =>
  match c with BC_EQ => (bv_unsigned r1 =? 11) && (bv_unsigned r2 =? 0) && (off =? 8) | _ => false end
| None => false end = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rtmb_B_slow_ok :
match YCbn.slow_block rtmb_B_tbl809d8 0x830d4 0x809e4 (Z_to_bv 5 11) with
| Some (u, xr, k) => (bv_unsigned u =? 12) && (bv_unsigned xr =? 18) && (k =? 0)
| None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Section site. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Lemma rtmb_B_809d8_gran : forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n < 8 ->
~ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 8.
Proof.
intros ly S W mem md p n HAR Hin Hn.
destruct (al_shadow _ _ (AR_laws_ok segs B) ly S W mem md p n HAR Hin) as [Hbs _].
unfold req_size in Hbs. replace (n =? 0) with false in Hbs by (symmetry; apply Z.eqb_neq; lia).
exact (rtmb_ra_gran_false _ _ p n Hbs Hn).
Qed.
Lemma rtmb_B_809d8_cell : forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
exists s, aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some s /\ saddr_ok p s /\
(s <> 0 -> 0 < s < 8 /\ p mod 8 < s).
Proof.
intros ly S W mem md p n HAR Hin Hn.
assert (Hrq : 1 <= req_size n) by (unfold req_size; destruct (n =? 0); lia).
destruct (rtmb_blk_ra segs B ly S W mem md p n p 1 HAR Hin ltac:(lia) ltac:(lia)) as [R _].
destruct (rtmb_ra_cell _ _ _ R) as (s & Hs & Hok). exists s. split; [exact Hs|]. split; [exact Hok|].
intros Hs0. exact (rtmb_ra_slow p s Hok Hs0).
Qed.
End site.

(* ---- the region route through the symbolic engine at 0x809d8 ----
   The input's metadata byte s (at shadow_of_addr SHADOW_OFF p, p = s2) is a one-byte region of the symbolic state,
   based on an extra atom (32) whose value is that address; a second extra atom (33) is the byte. The facts: atom 18
   (s2 = p) 8-aligned, atom 33 in [0, 7] (so the `lb` keeps the plain atom), and the alias ((s2 >> 3) + s4, atom 32).
   The `add` 0x809d4 rewrites a1 to atom 32 by the alias (YP0e.s_alu2), the `lb` is a plain region load, and no
   shadow obligation is raised. The engine stops at the `beqz` 0x809dc (a1 = atom 33 against 0) and at the slow
   block's `bge` 0x830d8 (a2 = p & 7 = 0 by p's alignment, against atom 33); the branch split takes each outcome; the
   error arm (0 >= s with s <> 0) dies by saddr_ok. The same state without the region makes the token path ask
   shadow 0 over p's whole granule (rtmb_B_809d8_gran: false for an input of 1 .. 7 bytes). A walk lane uses the route
   mid-run by adding the region, the alias fact keyed on the atoms of the registers holding p and SHADOW_OFF, and the
   byte's atom fact to its symbolic state; without p's alignment fact the `andi` stays p & 7 and the error arm needs
   YCbn.alu_and7 and the p mod 8 < s form of saddr_ok (rtmb_B_80fcc_step below does exactly that). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK0h YK0i YK1b YK1a.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0e YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI08 YA0o YCbm YA0q YI16.

Lemma rtmb_B_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* s4 (x20) holds SHADOW_OFF, so the shadow base is its own atom; no block shadow entry is used. *)
Definition RTMB_B_Bx : sv := SOff 20 0.
Definition RTMB_B_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* atom 18 = s2 = p (8-aligned, in the allocator's range); atom 33 = the metadata byte, in [0, 7];
   atom 32 = the address of that byte, declared equal to (s2 >> 3) + s4 *)
Definition rtmb_B_r_facts : facts :=
  mkFacts [(18%nat, mkAF 4096 0x800000000000 3); (33%nat, mkAF 0 7 0)] []
          [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 20 0), SOff 32 0)].
Definition rtmb_B_r_mem : smem := [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]].
Definition rtmb_B_r_ss : sstate := mkSS 0x809d0 sr_atoms rtmb_B_r_mem None rtmb_B_r_facts.
(* the registers the two live arms keep: all but a1 (x11) and a2 (x12) *)
Definition RTMB_B_KEEP : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;10;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.

Section route. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* Every register but a1 and a2 holds its entry value when the symbolic state keeps it as its own atom. *)
Lemma rtmb_B_keep_regs : forall E ss ms regs extra,
st_ok rsegs E ss ms -> env_agree 32 (Ereg regs extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) RTMB_B_KEEP = true ->
forall r : bv 5, bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs extra HS HA Hf r H11 H12.
destruct (Z.eq_dec (bv_unsigned r) 0) as [Hr0 | Hr0].
{ assert (Er : r = (0%bv : bv 5)) by (apply bv_eq; rewrite Hr0; vm_compute; reflexivity).
  subst r. unfold getr. rewrite bv_eqb_refl. reflexivity. }
apply (regs_kept_of_st_ok rsegs E ss ms regs extra RTMB_B_KEEP HS HA Hf r).
pose proof (u5_range r) as Hu.
rewrite <- (Z_to_bv_bv_unsigned 5 r).
assert (Hc : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/
bv_unsigned r = 5 \/ bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
bv_unsigned r = 10 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/ bv_unsigned r = 16 \/
bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/ bv_unsigned r = 31) by lia.
repeat match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd|Hd] end;
rewrite Hc; cbv [RTMB_B_KEEP]; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* The walk reaches 0x809e4, the load of the input byte, with every register but a1 and a2 as at 0x809d0, the same
   memory and the same model up to materialization; no premise asks the granule's other bytes to be addressable. *)
Lemma rtmb_B_809d8_step : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) p s,
getr regs (Z_to_bv 5 18) = w64 p ->
getr regs (Z_to_bv 5 20) = w64 SHADOW_OFF ->
p mod 8 = 0 -> 4096 <= p -> p + 8 <= kHighMemEnd ->
aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some s ->
saddr_ok p s ->
(forall regs' md',
   (forall r : bv 5, bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> getr regs' r = getr regs r) ->
   same_but_materialized md md' ->
   SRr rsegs W (cfg_at rsegs 0x809e4 regs' mem md') Q) ->
SRr rsegs W (cfg_at rsegs 0x809d0 regs mem md) Q.
Proof.
intros W regs mem md Q p s H18 H20 Hal Hlo Hhi Hav Hok K.
pose proof rtmb_B_wx as Hwx.
pose proof (rtmb_sok_range p s Hal Hok) as Hs7.
unfold kHighMemEnd in Hhi.
set (extra := [Z_to_bv 64 (shadow_of_addr SHADOW_OFF p); Z_to_bv 64 s]).
set (E := Ereg regs extra).
assert (Ew18 : ew E 18%nat = Z_to_bv 64 p).
{ unfold E. rewrite (ew_Ereg_nat regs extra 18%nat (Z_to_bv 5 18) eq_refl), H18. reflexivity. }
assert (Ew20 : ew E 20%nat = Z_to_bv 64 SHADOW_OFF).
{ unfold E. rewrite (ew_Ereg_nat regs extra 20%nat (Z_to_bv 5 20) eq_refl), H20. reflexivity. }
assert (Ew32 : ew E 32%nat = Z_to_bv 64 (SHADOW_OFF + p / 8)) by reflexivity.
assert (Ew33 : ew E 33%nat = Z_to_bv 64 s) by reflexivity.
assert (HG : facts_ok E rtmb_B_r_facts).
{ unfold facts_ok. split; [|split].
  - cbv [rtmb_B_r_facts f_atoms]. cbn [atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew18, unsigned_lit_small by lia.
      change (2 ^ 3) with 8. lia.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, unsigned_lit_small by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  - exact I.
  - cbv [rtmb_B_r_facts f_alias]. cbn [alias_ok]. split; [|exact I].
    exact (shadow_decl_ok E 18%nat 20%nat 32%nat p SHADOW_OFF Ew18 ltac:(lia) Ew20 Ew32). }
assert (HS : st_ok rsegs E rtmb_B_r_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x809d0) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rtmb_cell_region rsegs E (w_H W) mem 32%nat (SHADOW_OFF + p / 8) s (SOff 33 0)).
    + rewrite Ew32. apply unsigned_lit_small. unfold SHADOW_OFF. split; [lia|].
      assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). lia.
    + unfold shadow_of_addr in Hav. exact Hav.
    + cbn [sv_denot]. rewrite Ew33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    + unfold SHADOW_OFF. lia.
    + unfold SHADOW_OFF. assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). lia.
  - cbv [rtmb_B_r_ss rtmb_B_r_mem]. cbn [ss_mem pairwise_disjoint all_disjoint]. split; exact I.
  - exact HG. }
assert (SHOK : sh_ok rsegs RTMB_B_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs extra) E) by apply env_agree_refl.
unfold cfg_at. change (w64 0x809d0) with (Z_to_bv 64 0x809d0).
(* 0x809d0 .. 0x809d8, the region load, then the `beqz` *)
srr_run_tok rtmb_B_tbl809d8_ok HS SHOK RTMB_B_span.
assert (Em1 : ms_mem ms = mem)
  by (apply (frame_of_read_only E (ss_mem rtmb_B_r_ss) mem (ms_mem ms)); [vm_compute; reflexivity | exact HF]).
srr_branch_tok rtmb_B_tbl809d8_ok HS SHOK RTMB_B_span.
- (* the byte is 0: the check passes at once *)
  srr_run_to_tok rtmb_B_tbl809d8_ok HS SHOK RTMB_B_span 0x809e4.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms0 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems, Em2. apply K.
  + apply (rtmb_B_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
  + apply with_vm_backing_same.
- (* the byte is not 0: the slow block, then its `bge` *)
  assert (Hs0 : s <> 0).
  { intros Hz. cbn [sv_denot] in Hc. rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc by lia.
    rewrite Hz in Hc. vm_compute in Hc. discriminate. }
  pose proof (rtmb_sok_pos p s Hal Hok Hs0) as Hspos.
  srr_run_tok rtmb_B_tbl809d8_ok HS SHOK RTMB_B_span.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  srr_branch_tok rtmb_B_tbl809d8_ok HS SHOK RTMB_B_span.
  + (* the error path: p mod 8 >= the byte, which saddr_ok refuses *)
    exfalso. cbv [branch_taken] in Hc0. cbn [sv_denot] in Hc0.
    rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc0 by lia.
    rewrite YCbn.bv_lts_small in Hc0 by lia.
    apply negb_true_iff in Hc0. apply Z.ltb_nlt in Hc0. lia.
  + (* the check passes: back to 0x809e4 *)
    srr_run_to_tok rtmb_B_tbl809d8_ok HS SHOK RTMB_B_span 0x809e4.
    assert (Em3 : ms_mem ms1 = mem)
      by (rewrite <- Em2; refine (frame_of_read_only E _ _ _ _ HF1); vm_compute; reflexivity).
    pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms1 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    rewrite Ems, Em3. apply K.
    * apply (rtmb_B_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
    * apply with_vm_backing_same.
Qed.
End route.

(* ================= 8b. risk 2, the slow-block variant at 0x80fcc (P.sel, the property loop's key byte) =================
   The code, read from image B's loaded segments: 0x80fc4 srli a0,s2,3; 0x80fc8 add a0,a0,s4; 0x80fcc lb a0,0(a0);
   0x80fd0 beqz a0,+8; 0x80fd4 j 0x82594; 0x80fd8 lbu a1,0(s2); and the out-of-line block 0x82594 andi a1,s2,7;
   0x82598 blt a1,a0,+8; 0x8259c j 0x83440 (the report call: mv a0,s2; jal errpath_load1); 0x825a0 j 0x80fd8. s2 is the
   cursor x (in.p, after header and property bytes: no alignment fact), s4 the shadow offset. The block returns by a
   `blt` to a `j back`, which image A's code never does; YCbn.slow_block accepts neither the `beqz`'s fall-through
   (rtmb_B_tok80fcc_none) nor this block (rtmb_B_slow80fcc_none: its `blt` targets the `j`, not the return pc), so
   the token path asks shadow 0 over x's whole granule, false when x is in the input's partial last granule; the region
   route covers it. Four other checks use the same block form (0x81108, 0x81120, 0x81260, 0x812e0: copies into pp,
   whose shadow is 0 over the block, so the token path's None arm holds there). *)
Definition rtmb_B_tbl80fcc : ctable := build_table rsegs 0x80fc4 6 (build_table rsegs 0x82594 4 TEmpty).
Lemma rtmb_B_tbl80fcc_ok : table_ok rsegs rtmb_B_tbl80fcc.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

Lemma rtmb_B_tok80fcc_none : forall t, YCbn.slow_block rtmb_B_tbl80fcc 0x80fd4 0x80fd8 t = None.
Proof. intros t. vm_compute. reflexivity. Qed.
Lemma rtmb_B_slow80fcc_none : YCbn.slow_block rtmb_B_tbl80fcc 0x82594 0x80fd8 (Z_to_bv 5 10) = None.
Proof. vm_compute. reflexivity. Qed.

(* atom 18 = s2 = x (in the allocator's range, no alignment); atom 33 = the metadata byte, in [0, 7]; atom 32 = the
   address of that byte, declared equal to (s2 >> 3) + s4 *)
Definition rtmb_B_f_facts : facts :=
  mkFacts [(18%nat, mkAF 4096 0x800000000000 0); (33%nat, mkAF 0 7 0)] []
          [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 20 0), SOff 32 0)].
Definition rtmb_B_f_ss : sstate := mkSS 0x80fc4 sr_atoms rtmb_B_r_mem None rtmb_B_f_facts.
(* the registers the two live arms keep: all but a0 (x10) and a1 (x11) *)
Definition RTMB_B_KEEP01 : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.

Section route80fcc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma rtmb_B_keep01_regs : forall E ss ms regs extra,
st_ok rsegs E ss ms -> env_agree 32 (Ereg regs extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) RTMB_B_KEEP01 = true ->
forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs extra HS HA Hf r H10 H11.
destruct (Z.eq_dec (bv_unsigned r) 0) as [Hr0 | Hr0].
{ assert (Er : r = (0%bv : bv 5)) by (apply bv_eq; rewrite Hr0; vm_compute; reflexivity).
  subst r. unfold getr. rewrite bv_eqb_refl. reflexivity. }
apply (regs_kept_of_st_ok rsegs E ss ms regs extra RTMB_B_KEEP01 HS HA Hf r).
pose proof (u5_range r) as Hu.
rewrite <- (Z_to_bv_bv_unsigned 5 r).
assert (Hc : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/
bv_unsigned r = 5 \/ bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/ bv_unsigned r = 16 \/
bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/ bv_unsigned r = 31) by lia.
repeat match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd|Hd] end;
rewrite Hc; cbv [RTMB_B_KEEP01]; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* The walk reaches 0x80fd8, the load of the key byte, with every register but a0 and a1 as at 0x80fc4, the same
   memory and the same model up to materialization. x need not be aligned: the slow block's `andi` stays x & 7, which
   is x mod 8 (YCbn.alu_and7), and saddr_ok's x mod 8 < s kills the report arm. The shadow byte and saddr_ok come from
   the input's range_addressable (rtmb_in_ra, rtmb_ra_cell) at x = src + c, c < left. *)
Lemma rtmb_B_80fcc_step : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) x s,
getr regs (Z_to_bv 5 18) = w64 x ->
getr regs (Z_to_bv 5 20) = w64 SHADOW_OFF ->
4096 <= x -> x + 8 <= kHighMemEnd ->
aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x) = Some s ->
saddr_ok x s ->
(forall regs' md',
   (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr regs' r = getr regs r) ->
   same_but_materialized md md' ->
   SRr rsegs W (cfg_at rsegs 0x80fd8 regs' mem md') Q) ->
SRr rsegs W (cfg_at rsegs 0x80fc4 regs mem md) Q.
Proof.
intros W regs mem md Q x s H18 H20 Hlo Hhi Hav Hok K.
pose proof rtmb_B_wx as Hwx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
assert (Hs7 : 0 <= s <= 7) by (destruct Hok as [-> | [H1 H2]]; lia).
unfold kHighMemEnd in Hhi.
set (extra := [Z_to_bv 64 (shadow_of_addr SHADOW_OFF x); Z_to_bv 64 s]).
set (E := Ereg regs extra).
assert (Ew18 : ew E 18%nat = Z_to_bv 64 x).
{ unfold E. rewrite (ew_Ereg_nat regs extra 18%nat (Z_to_bv 5 18) eq_refl), H18. reflexivity. }
assert (Ew20 : ew E 20%nat = Z_to_bv 64 SHADOW_OFF).
{ unfold E. rewrite (ew_Ereg_nat regs extra 20%nat (Z_to_bv 5 20) eq_refl), H20. reflexivity. }
assert (Ew32 : ew E 32%nat = Z_to_bv 64 (SHADOW_OFF + x / 8)) by reflexivity.
assert (Ew33 : ew E 33%nat = Z_to_bv 64 s) by reflexivity.
assert (HG : facts_ok E rtmb_B_f_facts).
{ unfold facts_ok. split; [|split].
  - cbv [rtmb_B_f_facts f_atoms]. cbn [atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew18, unsigned_lit_small by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, unsigned_lit_small by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  - exact I.
  - cbv [rtmb_B_f_facts f_alias]. cbn [alias_ok]. split; [|exact I].
    exact (shadow_decl_ok E 18%nat 20%nat 32%nat x SHADOW_OFF Ew18 ltac:(lia) Ew20 Ew32). }
assert (HS : st_ok rsegs E rtmb_B_f_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80fc4) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rtmb_cell_region rsegs E (w_H W) mem 32%nat (SHADOW_OFF + x / 8) s (SOff 33 0)).
    + rewrite Ew32. apply unsigned_lit_small. unfold SHADOW_OFF. split; [lia|].
      assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
    + unfold shadow_of_addr in Hav. exact Hav.
    + cbn [sv_denot]. rewrite Ew33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    + unfold SHADOW_OFF. lia.
    + unfold SHADOW_OFF. assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
  - cbv [rtmb_B_f_ss rtmb_B_r_mem]. cbn [ss_mem pairwise_disjoint all_disjoint]. split; exact I.
  - exact HG. }
assert (SHOK : sh_ok rsegs RTMB_B_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs extra) E) by apply env_agree_refl.
unfold cfg_at. change (w64 0x80fc4) with (Z_to_bv 64 0x80fc4).
(* 0x80fc4 .. 0x80fcc, the region load, then the `beqz` *)
srr_run_tok rtmb_B_tbl80fcc_ok HS SHOK RTMB_B_span.
assert (Em1 : ms_mem ms = mem)
  by (apply (frame_of_read_only E (ss_mem rtmb_B_f_ss) mem (ms_mem ms)); [vm_compute; reflexivity | exact HF]).
srr_branch_tok rtmb_B_tbl80fcc_ok HS SHOK RTMB_B_span.
- (* the byte is 0: the check passes at once *)
  srr_run_to_tok rtmb_B_tbl80fcc_ok HS SHOK RTMB_B_span 0x80fd8.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms0 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems, Em2. apply K.
  + apply (rtmb_B_keep01_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
  + apply with_vm_backing_same.
- (* the byte is not 0: 0x80fd4 j 0x82594, the `andi`, then the `blt` *)
  assert (Hs0 : s <> 0).
  { intros Hz. cbn [sv_denot] in Hc. rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc by lia.
    rewrite Hz in Hc. vm_compute in Hc. discriminate. }
  srr_run_tok rtmb_B_tbl80fcc_ok HS SHOK RTMB_B_span.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  srr_branch_tok rtmb_B_tbl80fcc_ok HS SHOK RTMB_B_span.
  + (* x mod 8 < s: 0x825a0 j 0x80fd8, the check passes *)
    srr_run_to_tok rtmb_B_tbl80fcc_ok HS SHOK RTMB_B_span 0x80fd8.
    assert (Em3 : ms_mem ms1 = mem)
      by (rewrite <- Em2; refine (frame_of_read_only E _ _ _ _ HF1); vm_compute; reflexivity).
    pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms1 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    rewrite Ems, Em3. apply K.
    * apply (rtmb_B_keep01_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
    * apply with_vm_backing_same.
  + (* the error path 0x8259c: x mod 8 >= the byte, which saddr_ok refuses *)
    exfalso.
    assert (G : sv_denot E (SAlu ALU_AND (SOff 18 0) (SLit 7)) = Z_to_bv 64 (x mod 8)).
    { cbn [sv_denot]. rewrite Ew18, unsigned_lit_small, Z.add_0_r by lia. apply alu_and7. unfold M64. lia. }
    rewrite G in Hc0. cbn [sv_denot] in Hc0. rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc0 by lia.
    cbn [branch_taken] in Hc0. rewrite (rtmb_ra_slow_bv x s Hok Hs0) in Hc0. discriminate Hc0.
Qed.
End route80fcc.

Print Assumptions rtmb_bytes_patch.
Print Assumptions rtmb_bytes_field.
Print Assumptions rtmb_blk_ra.
Print Assumptions rtmb_blk_last.
Print Assumptions rtmb_ra_gran_false.
Print Assumptions rtmb_ra_cell_n.
Print Assumptions rtmb_ra_slow_n_bv.
Print Assumptions rtmb_ra_cell4.
Print Assumptions rtmb_cell_region.
Print Assumptions rtmb_stk_ra.
Print Assumptions rtmb_sh_t_in.
Print Assumptions rtmb_sh_e42_in.
Print Assumptions rtmb_sh_e62_out.
Print Assumptions rtmb_sh_hz_in.
Print Assumptions rtmb_fsh_set.
Print Assumptions rtmb_B_ra_r.
Print Assumptions rtmb_B_ra_e42.
Print Assumptions rtmb_B_ra_e62.
Print Assumptions rtmb_B_ra_hz.
Print Assumptions rtmb_fsh_of_chunks.
Print Assumptions rtmb_slots_chunk.
Print Assumptions rtmb_cut_kept.
Print Assumptions rtmb_keeps_call.
Print Assumptions rtmb_ask_join.
Print Assumptions rtmb_ask_split.
Print Assumptions rtmb_B_tok_none.
Print Assumptions rtmb_B_tok_arm.
Print Assumptions rtmb_B_slow_ok.
Print Assumptions rtmb_B_809d8_gran.
Print Assumptions rtmb_B_809d8_cell.
Print Assumptions rtmb_bytes_store.
Print Assumptions rtmb_pp_len.
Print Assumptions rtmb_pp_ent.
Print Assumptions rtmb_pp_buf.
Print Assumptions rtmb_ro_bytes.
Print Assumptions rtmb_ra_kept_wr.
Print Assumptions rtmb_rom_kept_wr.
Print Assumptions rtmb_ra_not_fsh.
Print Assumptions rtmb_shadow_not_app.
Print Assumptions rtmb_sh_P0_big.
Print Assumptions rtmb_sh_P0.
Print Assumptions rtmb_sh_PB.
Print Assumptions rtmb_B_rz.
Print Assumptions rtmb_sok_pos.
Print Assumptions rtmb_B_keep_regs.
Print Assumptions rtmb_B_809d8_step.
Print Assumptions rtmb_B_tok80fcc_none.
Print Assumptions rtmb_B_slow80fcc_none.
Print Assumptions rtmb_B_keep01_regs.
Print Assumptions rtmb_B_80fcc_step.
