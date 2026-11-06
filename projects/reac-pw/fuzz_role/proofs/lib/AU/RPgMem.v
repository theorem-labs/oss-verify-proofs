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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgMemB.v at dda1ad05d6e, ported to
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role; prefix rtmb_ -> rm_
   (rtmb_B_ -> rm_B_, the object hz -> role), RtPgBase's rt_ -> RPgBase's rl_, the segments lib/AU/Img0.v rsegs; every
   address is role B's (the frame description, the prologue and scope-store sites, the real frame of 0x200 bytes);
   risk 2 at role B's sites 0x8028c (E01, data[0]) and 0x8078c (P.sel, whose slow block is the `bge; j back` form). *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the memory and shadow layer of
   the walk of LLVMFuzzerTestOneInput (0x80020). Proves no function (kind: segment lemma). Every lemma is over the
   concrete state (aview, val_mem, garr8, the shadow bytes), generic in the segments segs, so that each walk piece can
   rebuild its symbolic regions from a cut's facts and give the facts back after its run, a store or a call.

   1. Byte lists: the little-endian value of a byte list and its bytes (le_byte), the bytes of Z_to_le_bytes.
   2. rm_bytes: a list of bytes at an address, the form of role_build_contract's and role_check_contract's garr8
      premises (pp's image, the input after the flags byte); kept, split, slice, patch (a store or a call's write
      inside the list), the value of a field, the bytes a store leaves; the fields of pp's image (len, is_props,
      has_params, params_struct, ent[i], n_ent, corrupt, buf) as the code loads them; read-only image bytes.
   3. Calls: what the memory-checking runtime's memset / memcpy wrappers leave (the memory part of
      YG0d.aintrin_realizes' post); the shadow premises of a block's bytes (pp, pod, the input), and the shadow byte of
      a block's partial last granule (the input's).
   4. Shadow checks. The engine's token path (lib/Reusable/YCbn.v tok_branch) follows a check's slow block only when
      it starts at the `bnez` target or at the `beqz` fall-through. Over the 105 instrumented checks of image B's
      LLVMFuzzerTestOneInput: 56 are `bnez t,L` with L = `andi u,x,7; [addi u,u,k]; blt u,t,back` (both outcomes
      followed), 22 are `beqz t,+8; j L` with L = `andi u,x,7; bge u,t,report; j back`, 16 are `beqz t,+8; j report`
      and 11 are `bnez t,report`. For the `beqz; j` forms the token path takes its None arm, which asks shadow 0 over
      the whole granule. That holds for every check except five input reads whose granule can be the input's last,
      partial one: 0x8028c (E01: data[0]), 0x802f8, 0x80350 (M01.pre), 0x8078c (P.sel), 0x80b18 (the count byte).
      There the walk puts the input's shadow byte in a region (rm_cell_region) and loads it as memory, splits the
      `beqz` and the slow block's branch, and rm_ra_cell / rm_ra_slow(_bv) kill the error-path arm; rm_ra_gran_false
      records why the token path's obligation cannot be paid there; section 8 checks the code and the facts at
      0x8028c and runs the route at 0x8028c (an 8-aligned cursor) and at 0x8078c (a cursor of any alignment).
      rm_ra_cell_n gives the shadow byte of an n-byte access inside one granule (the `bnez` checks of floats[20] and
      r[k]).
   5. The stack's zero shadow: the real-frame cells the code shadow-checks (parts[1]'s store8 check 0x80e30 at R+0x180,
      pod_nearest's out cell at R+0x178) from AR's zero-shadow ranges.
   6. The frame for locals F (class 4, request 704 in a 1024-byte frame; the prologue writes 88 of its 128 shadow
      bytes from shadow_addr F): t F+0x20 (96 bytes), ch F+0xa0 (24), r F+0xe0 (4), e F+0xf0 (104), e42 F+0x180 (104),
      e62 F+0x210 (104), role F+0x2a0 (4). rm_sh gives its shadow bytes in each scope state (the prologue's 88 stores
      0x80104-0x80264 and the scope-store groups after it); the checks and calls on the seven objects (r and role see
      the shadow byte 0x04 and pass on the slow path); the frame-shadow region's chunks.
   7. The real frame's 8-byte cells (R = s1) and RPgBase's cut facts (rl_at / rl_cut): kept across a step, a store
      or a call, and as engine chunks; a cell read as two 4-byte halves or the other way.
   8. Risk 2 at 0x8028c and 0x8078c, on image B's code: the token path's obligation, the site's facts, and the region
      route run through the symbolic engine from 0x80284 to 0x80298 (rm_B_8028c_step) and from 0x80784 to 0x80798
      with a cursor of unknown alignment (rm_B_8078c_step).
   9. A segment's start facts at the current memory (input bytes, their shadow bytes and hull, rom_view) across a
      write set, and the address facts that keep the input's shadow bytes out of it (the shadow band, P0's bytes). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP03.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YG0t.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0 RPgImgA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================== 1. byte lists ======================================== *)
Definition rm_slice (l : list byte) (o n : nat) : list byte := firstn n (skipn o l).

Lemma rm_lor_shift8 : forall a r, 0 <= a < 256 -> 0 <= r -> Z.lor a (Z.shiftl r 8) = a + 256 * r.
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

Lemma rm_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. change (bv_modulus 8) with 256 in H. exact H. Qed.

Lemma rm_lez_range : forall l, 0 <= bytes_le_to_Z l < 2 ^ (8 * Z.of_nat (length l)).
Proof.
induction l as [|b l IH]; [cbn; lia|].
cbn [bytes_le_to_Z length]. pose proof (rm_byte_range b) as Hb.
rewrite rm_lor_shift8 by lia.
rewrite Nat2Z.inj_succ, Z.mul_succ_r, Z.pow_add_r by lia. change (2 ^ 8) with 256. nia.
Qed.

Lemma rm_lez_cons : forall b l, bytes_le_to_Z (b :: l) = bv_unsigned b + 256 * bytes_le_to_Z l.
Proof.
intros b l. cbn [bytes_le_to_Z]. pose proof (rm_lez_range l). apply rm_lor_shift8; [apply rm_byte_range | lia].
Qed.

Lemma rm_lez_shiftr : forall l k, (k < length l)%nat ->
Z.shiftr (bytes_le_to_Z l) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
induction l as [|b l IH]; intros k Hk; cbn [length] in Hk; [lia|].
rewrite rm_lez_cons. pose proof (rm_byte_range b) as Hb. pose proof (rm_lez_range l) as Hl.
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

Lemma rm_lez_le_byte : forall l k, (k < length l)%nat ->
le_byte (bytes_le_to_Z l) (length l) k = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
intros l k Hk. unfold le_byte. rewrite (Z.mod_small (bytes_le_to_Z l)) by apply rm_lez_range.
apply rm_lez_shiftr. exact Hk.
Qed.

Lemma rm_le_byte_bv : forall v n k, (k < n)%nat ->
Z_to_bv 8 (le_byte v n k) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
intros v n k Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with (2 ^ 8). unfold le_byte. change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
apply Z.bits_inj'. intros i Hi. destruct (Z_lt_le_dec i 8) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma rm_nth_le_bytes : forall n v k, (k < n)%nat ->
nth k (Z_to_le_bytes n v) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros v k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- rewrite Nat2Z.inj_0, Z.mul_0_r, Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma rm_nth_map : forall (l : list byte) j,
nth j (map (fun x : byte => bv_unsigned x) l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|b l IH]; intros [|j]; cbn [map nth]; try reflexivity. apply IH. Qed.

Lemma rm_nth_repeat : forall (x d : byte) n i, (i < n)%nat -> nth i (repeat x n) d = x.
Proof. intros x d n. induction n as [|n IH]; intros [|i] Hi; cbn [repeat nth]; [lia | lia | reflexivity | apply IH; lia]. Qed.

Lemma rm_length_repeat : forall (x : byte) n, length (repeat x n) = n.
Proof. intros x n. induction n as [|n IH]; cbn [repeat length]; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma rm_unsigned_byte : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256.
Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma rm_le_byte_1 : forall v, 0 <= v < 256 -> le_byte v 1 0 = v.
Proof.
intros v Hv. unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.

Section mem. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* ==================================== 2. bytes at an address ==================================== *)
Definition rm_bytes (H : word -> bool) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
garr8 segs (mrestrict H mem) a (map (fun x : byte => bv_unsigned x) l).

Lemma rm_val1_aview : forall H mem x v,
val_mem segs (mrestrict H mem) x 1 v -> 0 <= v < 256 -> aview segs H mem x = Some v.
Proof.
intros H mem x v V R. specialize (V 0%nat ltac:(lia)). rewrite Z.add_0_r in V.
unfold aview. rewrite V. cbn [option_map]. f_equal. rewrite rm_unsigned_byte, rm_le_byte_1 by exact R.
apply Z.mod_small. exact R.
Qed.

Lemma rm_aview_mbyte : forall H mem x (b : byte),
aview segs H mem x = Some (bv_unsigned b) -> mbyte segs (mrestrict H mem) x = Some b.
Proof.
intros H mem x b A. unfold aview in A. destruct (mbyte segs (mrestrict H mem) x) as [b'|] eqn:E; [|discriminate A].
cbn [option_map] in A. injection A as A. f_equal. apply bv_eq. exact A.
Qed.

Lemma rm_aview_val1 : forall H mem x v,
aview segs H mem x = Some v -> val_mem segs (mrestrict H mem) x 1 v /\ 0 <= v < 256.
Proof.
intros H mem x v A. unfold aview in A. destruct (mbyte segs (mrestrict H mem) x) as [b|] eqn:E; [|discriminate A].
cbn [option_map] in A. injection A as <-. pose proof (rm_byte_range b) as R. split; [|exact R].
intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, E, rm_le_byte_1 by exact R.
f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rm_bytes_aview : forall H mem a l,
rm_bytes H mem a l <->
(forall i, (i < length l)%nat -> aview segs H mem (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0)))).
Proof.
intros H mem a l. unfold rm_bytes, garr8. rewrite length_map. split.
- intros G i Hi. destruct (G i Hi) as [V R]. rewrite rm_nth_map in V, R. exact (rm_val1_aview _ _ _ _ V R).
- intros A i Hi. rewrite rm_nth_map. exact (rm_aview_val1 _ _ _ _ (A i Hi)).
Qed.

Lemma rm_bytes_kept : forall H mem H' mem' a l,
rm_bytes H mem a l ->
(forall x, a <= x < a + Z.of_nat (length l) -> aview segs H' mem' x = aview segs H mem x) ->
rm_bytes H' mem' a l.
Proof.
intros H mem H' mem' a l B K. apply rm_bytes_aview. intros i Hi. rewrite K by lia.
exact (proj1 (rm_bytes_aview H mem a l) B i Hi).
Qed.

Lemma rm_bytes_app : forall H mem a l1 l2,
rm_bytes H mem a (l1 ++ l2) <-> rm_bytes H mem a l1 /\ rm_bytes H mem (a + Z.of_nat (length l1)) l2.
Proof. intros H mem a l1 l2. unfold rm_bytes. rewrite map_app, garr8_app, length_map. reflexivity. Qed.

Lemma rm_bytes_slice : forall H mem a l o n,
rm_bytes H mem a l -> (o + n <= length l)%nat -> rm_bytes H mem (a + Z.of_nat o) (rm_slice l o n).
Proof.
intros H mem a l o n B Hl. unfold rm_slice.
rewrite <- (firstn_skipn o l) in B. apply rm_bytes_app in B as [_ B].
rewrite length_firstn, Nat.min_l in B by lia.
rewrite <- (firstn_skipn n (skipn o l)) in B. apply rm_bytes_app in B as [B _]. exact B.
Qed.

Lemma rm_bytes_patch : forall H mem H' mem' a l o x,
rm_bytes H mem a l -> rm_bytes H' mem' (a + Z.of_nat o) x -> (o + length x <= length l)%nat ->
(forall y, a <= y < a + Z.of_nat (length l) -> ~ (a + Z.of_nat o <= y < a + Z.of_nat (o + length x)) ->
 aview segs H' mem' y = aview segs H mem y) ->
rm_bytes H' mem' a (Model.overwrite l o x).
Proof.
intros H mem H' mem' a l o x B X Hl K. unfold Model.overwrite.
assert (Lf : length (firstn o l) = o) by (rewrite length_firstn; lia).
rewrite <- (firstn_skipn o l) in B. apply rm_bytes_app in B as [B1 B2]. rewrite Lf in B2.
rewrite <- (firstn_skipn (length x) (skipn o l)) in B2. apply rm_bytes_app in B2 as [_ B3].
rewrite length_firstn, length_skipn, Nat.min_l in B3 by lia. rewrite skipn_skipn in B3.
apply rm_bytes_app. split.
- apply (rm_bytes_kept H mem); [exact B1|]. intros y Hy. rewrite Lf in Hy. apply K; lia.
- rewrite Lf. apply rm_bytes_app. split; [exact X|].
  replace (a + Z.of_nat o + Z.of_nat (length x)) with (a + Z.of_nat o + Z.of_nat (length x)) by reflexivity.
  replace (o + length x)%nat with (length x + o)%nat by lia.
  apply (rm_bytes_kept H mem); [exact B3|]. intros y Hy.
  rewrite length_skipn in Hy. apply K; lia.
Qed.

Lemma rm_bytes_val : forall H mem a l,
rm_bytes H mem a l -> val_mem segs (mrestrict H mem) a (length l) (bytes_le_to_Z l).
Proof.
intros H mem a l B k Hk. pose proof (proj1 (rm_bytes_aview H mem a l) B k Hk) as A.
rewrite (rm_aview_mbyte _ _ _ _ A). f_equal. rewrite rm_lez_le_byte by exact Hk.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma rm_bytes_of_val : forall H mem a n v,
val_mem segs (mrestrict H mem) a n v -> rm_bytes H mem a (Z_to_le_bytes n v).
Proof.
intros H mem a n v V. apply rm_bytes_aview. intros i Hi. rewrite length_Z_to_le_bytes in Hi.
rewrite rm_nth_le_bytes by exact Hi. unfold aview. rewrite (V i Hi). cbn [option_map].
rewrite rm_le_byte_bv by exact Hi. reflexivity.
Qed.

Lemma rm_val_of_bytes : forall H mem a n v,
rm_bytes H mem a (Z_to_le_bytes n v) -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros H mem a n v B k Hk. pose proof (proj1 (rm_bytes_aview _ _ _ _) B k) as A.
rewrite length_Z_to_le_bytes in A. specialize (A Hk). rewrite rm_nth_le_bytes in A by exact Hk.
rewrite (rm_aview_mbyte _ _ _ _ A). rewrite rm_le_byte_bv by exact Hk. reflexivity.
Qed.

Lemma rm_bytes_field : forall H mem a l o n v,
rm_bytes H mem a l -> rm_slice l o n = Z_to_le_bytes n v -> (o + n <= length l)%nat ->
val_mem segs (mrestrict H mem) (a + Z.of_nat o) n v.
Proof.
intros H mem a l o n v B E Hl. apply rm_val_of_bytes. rewrite <- E. apply rm_bytes_slice; assumption.
Qed.

Lemma rm_bytes_byte : forall H mem a l c,
rm_bytes H mem a l -> (c < length l)%nat ->
val_mem segs (mrestrict H mem) (a + Z.of_nat c) 1 (bv_unsigned (nth c l (Z_to_bv 8 0))).
Proof.
intros H mem a l c B Hc. unfold rm_bytes, garr8 in B. rewrite length_map in B.
destruct (B c Hc) as [V _]. rewrite rm_nth_map in V. exact V.
Qed.

(* A store of the n-byte value v at a + o inside the list (a put32 / patch32 byte, a len8 store, a flag word). *)
Lemma rm_bytes_store : forall H mem H' mem' a l o n v,
rm_bytes H mem a l -> val_mem segs (mrestrict H' mem') (a + Z.of_nat o) n v -> (o + n <= length l)%nat ->
(forall y, a <= y < a + Z.of_nat (length l) -> ~ (a + Z.of_nat o <= y < a + Z.of_nat (o + n)) ->
 aview segs H' mem' y = aview segs H mem y) ->
rm_bytes H' mem' a (Model.overwrite l o (Z_to_le_bytes n v)).
Proof.
intros H mem H' mem' a l o n v B V Hl K.
apply (rm_bytes_patch H mem); [exact B | apply rm_bytes_of_val; exact V | rewrite length_Z_to_le_bytes; exact Hl |].
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
Lemma rm_pp_len_img : Z.of_nat (length IMG) = Layout.PP_SIZE.
Proof. unfold IMG. apply Layout.length_pp_image; assumption. Qed.

Lemma rm_pp_field : forall H mem pp off n v,
rm_bytes H mem pp IMG -> rm_slice IMG (Z.to_nat off) n = Z_to_le_bytes n v -> 0 <= off ->
off + Z.of_nat n <= Layout.PP_SIZE ->
val_mem segs (mrestrict H mem) (pp + off) n v.
Proof.
intros H mem pp off n v B E H0 H1. pose proof rm_pp_len_img as L.
replace (pp + off) with (pp + Z.of_nat (Z.to_nat off)) by lia.
apply (rm_bytes_field H mem pp IMG); [exact B | exact E | lia].
Qed.

Lemma rm_pp_len : forall H mem pp, rm_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_LEN) 8 (Z.of_nat (length b)).
Proof.
intros H mem pp B. apply (rm_pp_field H mem pp); [exact B | | unfold Layout.OFF_LEN; lia | unfold Layout.OFF_LEN, Layout.PP_SIZE; lia].
unfold rm_slice, IMG. eapply Layout.pp_read_len; eassumption.
Qed.
Lemma rm_pp_is_props : forall H mem pp, rm_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_IS_PROPS) 4 (Z.b2z isp).
Proof.
intros H mem pp B. apply (rm_pp_field H mem pp); [exact B | | unfold Layout.OFF_IS_PROPS; lia | unfold Layout.OFF_IS_PROPS, Layout.PP_SIZE; lia].
unfold rm_slice, IMG. eapply Layout.pp_read_is_props; eassumption.
Qed.
Lemma rm_pp_has_params : forall H mem pp, rm_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_HAS_PARAMS) 4 (Z.b2z hasp).
Proof.
intros H mem pp B. apply (rm_pp_field H mem pp); [exact B | | unfold Layout.OFF_HAS_PARAMS; lia | unfold Layout.OFF_HAS_PARAMS, Layout.PP_SIZE; lia].
unfold rm_slice, IMG. eapply Layout.pp_read_has_params; eassumption.
Qed.
Lemma rm_pp_params_struct : forall H mem pp, rm_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_PARAMS_STRUCT) 4 (Z.b2z pst).
Proof.
intros H mem pp B. apply (rm_pp_field H mem pp); [exact B | | unfold Layout.OFF_PARAMS_STRUCT; lia | unfold Layout.OFF_PARAMS_STRUCT, Layout.PP_SIZE; lia].
unfold rm_slice, IMG. eapply Layout.pp_read_params_struct; eassumption.
Qed.
Lemma rm_pp_n_ent : forall H mem pp, rm_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_N_ENT) 4 (Z.of_nat (length es)).
Proof.
intros H mem pp B. apply (rm_pp_field H mem pp); [exact B | | unfold Layout.OFF_N_ENT; lia | unfold Layout.OFF_N_ENT, Layout.PP_SIZE; lia].
unfold rm_slice, IMG. eapply Layout.pp_read_n_ent; eassumption.
Qed.
Lemma rm_pp_corrupt : forall H mem pp, rm_bytes H mem pp IMG ->
val_mem segs (mrestrict H mem) (pp + Layout.OFF_CORRUPT) 4 (Z.b2z corr).
Proof.
intros H mem pp B. apply (rm_pp_field H mem pp); [exact B | | unfold Layout.OFF_CORRUPT; lia | unfold Layout.OFF_CORRUPT, Layout.PP_SIZE; lia].
unfold rm_slice, IMG. eapply Layout.pp_read_corrupt; eassumption.
Qed.
Lemma rm_pp_ent : forall H mem pp i, rm_bytes H mem pp IMG -> (i < length es)%nat ->
rm_bytes H mem (pp + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i)) (Layout.ent_mem (nth i es (Model.Ent 0 0 []))).
Proof.
intros H mem pp i B Hi. pose proof rm_pp_len_img as L.
replace (pp + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i))
with (pp + Z.of_nat (Z.to_nat (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i)))
by (unfold Layout.OFF_ENT, Layout.ENT_SIZE; lia).
pose proof (Layout.pp_read_ent b isp hasp pst es corr) as Er.
repeat lazymatch type of Er with
| Z.of_nat (length b) <= _ -> _ => specialize (Er Hb)
| (length es <= 32)%nat -> _ => specialize (Er He)
| Forall _ es -> _ => specialize (Er Hs) end.
rewrite <- (Er i Hi).
apply (rm_bytes_slice H mem pp IMG (Z.to_nat (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat i)) 104); [exact B|].
unfold Layout.OFF_ENT, Layout.ENT_SIZE, Layout.PP_SIZE in *. pose proof He. lia.
Qed.
Lemma rm_pp_buf : forall H mem pp k n, rm_bytes H mem pp IMG -> (k + n <= length b)%nat ->
rm_bytes H mem (pp + Z.of_nat k) (rm_slice b k n).
Proof.
intros H mem pp k n B Hk. pose proof rm_pp_len_img as L. unfold IMG in *.
assert (E : rm_slice b k n = rm_slice (Layout.pp_image b isp hasp pst es corr) k n).
{ unfold rm_slice, Layout.pp_image. rewrite skipn_app. replace (k - length b)%nat with 0%nat by lia.
  cbn [skipn]. rewrite firstn_app, length_skipn. replace (n - (length b - k))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity. }
rewrite E. apply rm_bytes_slice; [exact B|].
rewrite <- (Nat2Z.id (length (Layout.pp_image b isp hasp pst es corr))), L.
unfold Layout.PP_SIZE, Layout.POD_BUF_MAX in *. lia.
Qed.
End pp.

(* Read-only data the code loads without a check or after one (the tables ints 0x21040 / floats 0x210a0 / t 0x21120 /
   t.11 0x21140 in .rodata, vocab 0x9a7a0 / odd_ch 0x9a820 / param 0x9a8c0 in .data.rel.ro, the jump table at 0x20ed4):
   the image's bytes, by the harness pre's arodata_okP (RPgBase; rl_seg_pre carries it), as rm_bytes of the list l
   the segments hold there. *)
Lemma rm_ro_bytes : forall B RLO RHI H mem a (l : list byte),
arodata_okP segs RLO RHI B (aview segs H mem) ->
(forall i, 0 <= i < Z.of_nat (length l) -> in_roP segs RLO RHI (a + i) /\
 ~ Exists (in_zr (a + i)) (as_owned_static B) /\ ~ (as_errno B <= a + i < as_errno B + 4)) ->
(forall i, (i < length l)%nat -> seg_rom segs (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i l (Z_to_bv 8 0))) ->
rm_bytes H mem a l.
Proof.
intros B RLO RHI H mem a l Hro Hin Hrom. apply rm_bytes_aview. intros i Hi.
destruct (Hin (Z.of_nat i) ltac:(lia)) as (H1 & H2 & H3). rewrite (Hro _ H1 H2 H3), (Hrom i Hi). reflexivity.
Qed.

(* ========================================== 3. calls ========================================== *)
Lemma rm_memset_bytes : forall H' mem' d c n,
(forall i, 0 <= i < Z.of_nat n -> aview segs H' mem' (d + i) = Some (c mod 256)) ->
rm_bytes H' mem' d (repeat (Z_to_bv 8 c) n).
Proof.
intros H' mem' d c n A. apply rm_bytes_aview. intros i Hi. rewrite rm_length_repeat in Hi.
rewrite rm_nth_repeat by exact Hi. rewrite rm_unsigned_byte. apply A. lia.
Qed.

Lemma rm_memcpy_bytes : forall H mem H' mem' x d l,
rm_bytes H mem x l ->
(forall i, 0 <= i < Z.of_nat (length l) -> aview segs H' mem' (d + i) = aview segs H mem (x + i)) ->
rm_bytes H' mem' d l.
Proof.
intros H mem H' mem' x d l B A. apply rm_bytes_aview. intros i Hi. rewrite A by lia.
exact (proj1 (rm_bytes_aview _ _ _ _) B i Hi).
Qed.

Lemma rm_hull_sub : forall (rd : reader) x n y k,
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
Lemma rm_blk_ra : forall ly S W mem md p m a n,
AR segs B ly S W mem md -> In (p, m) (ablocks B ly S) -> p <= a -> a + n <= p + req_size m ->
range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\
(0 < n -> shadow_hull_vis (aview segs (w_H W) mem) a n).
Proof.
intros ly S W mem md p m a n HAR Hin Hpa Han. split.
- exact (range_addressable_of_block segs B (AR_laws_ok segs B) ly S W mem md p m a n HAR Hin Hpa Han).
- intros Hn. destruct (al_shadow _ _ (AR_laws_ok segs B) ly S W mem md p m HAR Hin) as [_ Hh].
  exact (rm_hull_sub _ p (req_size m) a n Hh Hpa Han Hn).
Qed.
(* The shadow byte of a block's partial last granule: m mod 8 (the input block). *)
Lemma rm_blk_last : forall ly S W mem md p m,
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
Lemma rm_ra_cell : forall (rd : reader) K x,
range_addressable rd K x 1 -> exists s, rd (shadow_of_addr K x) = Some s /\ saddr_ok x s.
Proof. intros rd K x R. exact (R x ltac:(lia)). Qed.

Lemma rm_ra_slow : forall x s, saddr_ok x s -> s <> 0 -> 0 < s < 8 /\ x mod 8 < s.
Proof. intros x s [E|[H1 H2]] Hs; [lia|]. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

Lemma rm_ra_slow_bv : forall x s, saddr_ok x s -> s <> 0 ->
bv_lts (Z_to_bv 64 (x mod 8)) (Z_to_bv 64 s) = true.
Proof.
intros x s Hok Hs. destruct (rm_ra_slow x s Hok Hs) as [H1 H2]. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
rewrite YCbn.bv_lts_small by lia. apply Z.ltb_lt. exact H2.
Qed.

Lemma rm_ra_lb : forall s, 0 <= s < 128 -> v_lb (Z_to_bv 8 s) = Z_to_bv 64 s.
Proof.
intros s Hs. exact (YCbn.cellval_small true (Z_to_bv 8 s) s ltac:(rewrite rm_unsigned_byte; apply Z.mod_small; lia) Hs).
Qed.

Lemma rm_ra_gran_false : forall (rd : reader) K p n,
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
Lemma rm_cell_region : forall E H mem (k : nat) sa s e,
bv_unsigned (ew E k) = sa -> aview segs H mem sa = Some s -> sv_denot E e = Z_to_bv 64 s ->
0 <= sa -> sa < 2 ^ 64 ->
region_ok segs E (mrestrict H mem) (YP09.mkRegion (Some k) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 e)]).
Proof.
intros E H mem k sa s e Hk A He H0 H1. destruct (rm_aview_val1 _ _ _ _ A) as [V R].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hk. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor]. apply (chunk_ok_val segs E _ sa 0 1 e s He); [cbn; lia | lia |].
rewrite Z.add_0_r. exact V.
Qed.

(* A region without a write window at the address held by atom k, with chunks cs. *)
Lemma rm_ro_region : forall E H mem (k : nat) b lo hi cs,
bv_unsigned (ew E k) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
Forall (YP09.chunk_ok segs E (mrestrict H mem) b) cs ->
region_ok segs E (mrestrict H mem) (YP09.mkRegion (Some k) lo hi 0 0 cs).
Proof.
intros E H mem k b lo hi cs Hk H0 H1 C. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hk. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | exact C].
Qed.

(* The same with the write window [wlo, whi), whose bytes are present (a block, a frame, the stack). *)
Lemma rm_rw_region : forall E H mem (k : nat) b lo hi wlo whi cs,
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

Lemma rm_in_ra : forall (rd : reader) K src left c,
range_addressable rd K src left -> 0 <= c < left -> range_addressable rd K (src + c) 1.
Proof. intros rd K src left c R Hc. eapply range_addressable_sub; [exact R | lia | lia]. Qed.

(* An n-byte access at x inside one granule (x mod 8 + n <= 8), its bytes addressable: the shadow byte s of x's
   granule is 0, or 0 < s < 8 with the access's last offset x mod 8 + n - 1 below s, so the `bnez` check's slow block
   `andi u,x,7; addi u,u,n-1; blt u,t,back` returns (floats[20], r[k]). *)
Lemma rm_ra_cell_n : forall (rd : reader) K x n,
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
Lemma rm_ra_slow_n_bv : forall x n s, 0 < n -> x mod 8 + n <= 8 -> 0 < s < 8 -> x mod 8 + n - 1 < s ->
bv_lts (Z_to_bv 64 (x mod 8 + (n - 1))) (Z_to_bv 64 s) = true.
Proof.
intros x n s Hn Hg Hs Hl. pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
rewrite YCbn.bv_lts_small by lia. apply Z.ltb_lt. lia.
Qed.

(* a 4-byte access at an 8-aligned address (floats[20] at 0x210f0: 4 usable bytes) *)
Lemma rm_ra_cell4 : forall (rd : reader) K a,
range_addressable rd K a 4 -> a mod 8 = 0 ->
exists s, rd (shadow_of_addr K a) = Some s /\ (s = 0 \/ 3 < s < 8).
Proof.
intros rd K a R Ha. destruct (rm_ra_cell_n rd K a 4 R ltac:(lia) ltac:(lia)) as (s & Hs & Hc).
exists s. split; [exact Hs|]. lia.
Qed.

(* saddr_ok at an 8-aligned address: the byte is 0 or strictly between 0 and 8 *)
Lemma rm_sok_range : forall p s, p mod 8 = 0 -> saddr_ok p s -> 0 <= s <= 7.
Proof. intros p s Hp [->|[H1 H2]]; [lia|]. rewrite Hp in H1. lia. Qed.
Lemma rm_sok_pos : forall p s, p mod 8 = 0 -> saddr_ok p s -> s <> 0 -> 0 < s.
Proof. intros p s Hp [->|[H1 H2]] Hs; [lia|]. rewrite Hp in H1. lia. Qed.

(* ================================== 5. the stack's zero shadow ================================== *)
Section stk.
Variable B : asyms.
Lemma rm_stk_ra : forall ly S W mem md a n h,
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

(* The real-frame cells image B shadow-checks (hi_rz: [R+0x178, R+0x188)): parts[1]'s store8 check 0x80e24-0x80e3c
   before the store 0x80e48 at R+0x180, and pod_nearest's out cell at R+0x178 (its store8 check is in
   pod_nearest). R + 0x200 <= h: the real frame lies below the entry sp (`addi sp,sp,-0x200` 0x80020). *)
Lemma rm_B_rz : forall ly S W mem md R h,
AR segs B ly S W mem md -> ly_stk_lo ly <= R -> R + 0x200 <= h -> h <= ly_stk_hi ly -> h mod 8 = 0 ->
Forall (fun z => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (R + fst z) (snd z)) (hi_rz role_himg_B).
Proof.
intros ly S W mem md R h HAR Hlo Hh Hhi H8. change (hi_rz role_himg_B) with [(0x178, 16)]. constructor; [|constructor].
cbn [fst snd]. apply (rm_stk_ra ly S W mem md _ _ h HAR); lia.
Qed.

End stk.

(* ================================ 6. the frame for locals (image B) ================================
   The class-4 frame F (frame_alloc_4(704) 0x80090; 1024 bytes, 128 shadow bytes): the frame description at .rodata
   0x18dd9 reads "7 32 96 7 t.i.i.i 160 24 8 ch.i.i.i 224 4 7 r.i.i.i 240 104 3 e.i 384 104 5 e42.i 528 104 5 e62.i
   672 4 8 role:147". e is the shape-7 Int pod of pod.h:403, e42 the Int-7 pod of pod.h:413, e62 the count loop's pod
   of pod.h:426 (pod_write_ent takes each e by address: 0x80818 e, 0x81c08 e42, 0x81908 e62). role is the int of
   fuzz_role.c:147. *)
Definition RM_T : Z := 0x20.
Definition RM_CH : Z := 0xa0.
Definition RM_R : Z := 0xe0.
Definition RM_E : Z := 0xf0.
Definition RM_E42 : Z := 0x180.
Definition RM_E62 : Z := 0x210.
Definition RM_ROLE : Z := 0x2a0.

(* The 88 shadow bytes of F the prologue writes, in a scope state: t (granules 0x04-0x0f), ch (0x14-0x16), e
   (0x1e-0x2a), e42 (0x30-0x3c), e62 (0x42-0x4e) are 0x00 in scope; r (0x1c) and ro = role (0x54) are 0x04 (4 bytes
   usable); out of scope 0xf8; the guards 0xf1 (0x00-0x03), 0xf2 (0x10-0x13, 0x17-0x1b, 0x1d, 0x2b-0x2f, 0x3d-0x41,
   0x4f-0x53), 0xf3 (0x55-0x57). Measured on the prologue's 88 stores 0x80104-0x80264 (each `sb` off s3 =
   shadow_addr F with a3 = 0xf1, a0 = 0xf8, a1 = 0xf2, a2 = 0xf3). Shadow bytes 0x58-0x7f of the frame are not
   written there and no access reaches F + 704 .. F + 1024. *)
Definition rm_sh (t ch r e e42 e62 ro : bool) : list Z :=
repeat 0xf1 4 ++ repeat (if t then 0 else 0xf8) 12 ++ repeat 0xf2 4 ++ repeat (if ch then 0 else 0xf8) 3 ++
repeat 0xf2 5 ++ [if r then 4 else 0xf8] ++ [0xf2] ++ repeat (if e then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++
repeat (if e42 then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++ repeat (if e62 then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++
[if ro then 4 else 0xf8] ++ repeat 0xf3 3.

Lemma rm_sh_len : forall t ch r e e42 e62 ro, length (rm_sh t ch r e e42 e62 ro) = 88%nat.
Proof. intros [] [] [] [] [] [] []; reflexivity. Qed.
(* P0 (C1, C2, C3, J8258c) and PB (C4: role in scope, the granule set to 0x04 at 0x82194) as image B's record
   holds them *)
Lemma rm_sh_P0 : rm_sh false false false false false false false = hi_shA role_himg_B.
Proof. vm_compute. reflexivity. Qed.
Lemma rm_sh_PB : rm_sh false false false false false false true = hi_shB role_himg_B.
Proof. vm_compute. reflexivity. Qed.
Lemma rm_sh_bytes : forall t ch r e e42 e62 ro, Forall (fun v => 0 <= v < 256) (rm_sh t ch r e e42 e62 ro).
Proof.
intros t ch r e e42 e62 ro. apply Forall_forall. intros v Hv.
assert (Hb : forallb (fun v => (0 <=? v) && (v <? 256)) (rm_sh t ch r e e42 e62 ro) = true)
  by (destruct t, ch, r, e, e42, e62, ro; vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb v Hv). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(* entries j .. j+k-1 of pat set to v *)
Definition rm_setn (pat : list Z) (j k : nat) (v : Z) : list Z :=
map (fun i => if (j <=? i)%nat && (i <? j + k)%nat then v else nth i pat 0) (seq 0 (length pat)).

Lemma rm_setn_len : forall pat j k v, length (rm_setn pat j k v) = length pat.
Proof. intros. unfold rm_setn. rewrite length_map, length_seq. reflexivity. Qed.

Lemma rm_nth_setn : forall pat j k v i, (i < length pat)%nat ->
nth i (rm_setn pat j k v) 0 = if (j <=? i)%nat && (i <? j + k)%nat then v else nth i pat 0.
Proof.
intros pat j k v i Hi. unfold rm_setn.
set (f := fun i0 : nat => if (j <=? i0)%nat && (i0 <? j + k)%nat then v else nth i0 pat 0).
rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

(* The scope-store sites, as patterns (store groups measured on image B's code, each `sb` off s3 = shadow_addr F with
   the value set just before): e in 0x807b4-0x807e4 (pod.h:403) / out 0x8082c-0x80860 (pod.h:406); e62 in
   0x80b58-0x80b88 (pod.h:426, each count turn) / out 0x8197c-0x819b4 and 0x81c94-0x81cc8 (pod.h:433); t in
   0x80c14-0x80c40 and 0x80c88-0x80cb4 (pod.h:233); ch in 0x80ccc-0x80cd4 and 0x815c4-0x815cc (pod.h:235); r in
   0x80cf0 (4, pod.h:238) / out 0x80dc4 (s10 = -8, pod.h:246);
   t and ch out 0x80ee8-0x80f20 (pod.h:262); e42 in 0x81b98-0x81bc8 (pod.h:413) / out 0x81c44-0x81c78 (pod.h:420);
   role in 0x82194 (4, fuzz_role.c:147) / out 0x82584 (fuzz_role.c:168). *)
Lemma rm_sh_t_in : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 4 12 0 = rm_sh true ch r e e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_t_out : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 4 12 0xf8 = rm_sh false ch r e e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_ch_in : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 20 3 0 = rm_sh t true r e e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_ch_out : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 20 3 0xf8 = rm_sh t false r e e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_r_in : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 28 1 4 = rm_sh t ch true e e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_r_out : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 28 1 0xf8 = rm_sh t ch false e e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e_in : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 30 13 0 = rm_sh t ch r true e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e_out : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 30 13 0xf8 = rm_sh t ch r false e42 e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e42_in : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 48 13 0 = rm_sh t ch r e true e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e42_out : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 48 13 0xf8 = rm_sh t ch r e false e62 ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e62_in : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 66 13 0 = rm_sh t ch r e e42 true ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e62_out : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 66 13 0xf8 = rm_sh t ch r e e42 false ro.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_role_in : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 84 1 4 = rm_sh t ch r e e42 e62 true.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_role_out : forall t ch r e e42 e62 ro,
rm_setn (rm_sh t ch r e e42 e62 ro) 84 1 0xf8 = rm_sh t ch r e e42 e62 false.
Proof. intros [] [] [] [] [] [] []; vm_compute; reflexivity. Qed.

Lemma rm_fsh_kept : forall H mem H' mem' F pat,
rl_fsh segs H mem F pat ->
(forall i, 0 <= i < Z.of_nat (length pat) ->
 aview segs H' mem' (shadow_addr F + i) = aview segs H mem (shadow_addr F + i)) ->
rl_fsh segs H' mem' F pat.
Proof. intros H mem H' mem' F pat P K i Hi. rewrite K by exact Hi. exact (P i Hi). Qed.

Lemma rm_fsh_set : forall H mem H' mem' F pat j k v,
rl_fsh segs H mem F pat ->
(forall i, Z.of_nat j <= i < Z.of_nat (j + k) -> aview segs H' mem' (shadow_addr F + i) = Some v) ->
(forall i, 0 <= i < Z.of_nat (length pat) -> ~ (Z.of_nat j <= i < Z.of_nat (j + k)) ->
 aview segs H' mem' (shadow_addr F + i) = aview segs H mem (shadow_addr F + i)) ->
rl_fsh segs H' mem' F (rm_setn pat j k v).
Proof.
intros H mem H' mem' F pat j k v P Sv K i Hi. rewrite rm_setn_len in Hi.
rewrite rm_nth_setn by lia.
destruct ((j <=? Z.to_nat i)%nat && (Z.to_nat i <? j + k)%nat) eqn:Ein.
- apply andb_prop in Ein as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. apply Sv. lia.
- assert (Hn : ~ (Z.of_nat j <= i < Z.of_nat (j + k))).
  { intros [E1 E2]. apply andb_false_iff in Ein as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia. }
  rewrite (K i Hi Hn). exact (P i Hi).
Qed.

Lemma rm_fsh_ra : forall H mem F pat o n,
rl_fsh segs H mem F pat -> F mod 8 = 0 -> 0 <= o -> o + n <= 8 * Z.of_nat (length pat) ->
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

Lemma rm_nth_range : forall pat (a len : nat) (z : Z),
forallb (fun g => nth g pat 0 =? z) (seq a len) = true -> forall g, (a <= g < a + len)%nat -> nth g pat 0 = z.
Proof.
intros pat a len z H g Hg. rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_seq. lia.
Qed.

(* An object of len granules from granule g0, every granule's shadow byte v: 0 (any bytes of it usable), or a single
   granule with 0 < v < 8 (its first v bytes usable). *)
Lemma rm_fsh_ra_obj : forall H mem F pat (g0 len : nat) v o n,
rl_fsh segs H mem F pat -> F mod 8 = 0 -> (g0 + len <= length pat)%nat ->
(forall g, (g0 <= g < g0 + len)%nat -> nth g pat 0 = v) ->
0 <= o -> o + n <= 8 * Z.of_nat len -> (v = 0 \/ (len = 1%nat /\ 0 < v < 8 /\ o + n <= v)) ->
range_addressable (aview segs H mem) SHADOW_OFF (F + 8 * Z.of_nat g0 + o) n.
Proof.
intros H mem F pat g0 len v o n P HF Hl Hv Ho Hn Hc.
replace (F + 8 * Z.of_nat g0 + o) with (F + (8 * Z.of_nat g0 + o)) by lia.
apply (rm_fsh_ra H mem F pat); [exact P | exact HF | lia | lia |].
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
   AR_frames_law gives F mod 32 = 0. e, e42 and e62 are the q of pod_write_ent's three calls (0x80818, 0x81c08,
   0x81908): its 104 bytes are addressable while the object is in scope. *)
Lemma rm_B_ra_t : forall H mem F ch r e e42 e62 ro o n,
rl_fsh segs H mem F (rm_sh true ch r e e42 e62 ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 96 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_T + o) n.
Proof.
intros H mem F ch r e e42 e62 ro o n P HF Ho Hn. unfold RM_T. change 0x20 with (8 * Z.of_nat 4).
apply (rm_fsh_ra_obj H mem F _ 4 12 0 o n P HF); [rewrite rm_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rm_nth_range _ 4 12); [|lia]. destruct ch, r, e, e42, e62, ro; vm_compute; reflexivity.
Qed.

Lemma rm_B_ra_ch : forall H mem F t r e e42 e62 ro o n,
rl_fsh segs H mem F (rm_sh t true r e e42 e62 ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 24 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_CH + o) n.
Proof.
intros H mem F t r e e42 e62 ro o n P HF Ho Hn. unfold RM_CH. change 0xa0 with (8 * Z.of_nat 20).
apply (rm_fsh_ra_obj H mem F _ 20 3 0 o n P HF); [rewrite rm_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rm_nth_range _ 20 3); [|lia]. destruct t, r, e, e42, e62, ro; vm_compute; reflexivity.
Qed.

Lemma rm_B_ra_e : forall H mem F t ch r e42 e62 ro o n,
rl_fsh segs H mem F (rm_sh t ch r true e42 e62 ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_E + o) n.
Proof.
intros H mem F t ch r e42 e62 ro o n P HF Ho Hn. unfold RM_E. change 0xf0 with (8 * Z.of_nat 30).
apply (rm_fsh_ra_obj H mem F _ 30 13 0 o n P HF); [rewrite rm_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rm_nth_range _ 30 13); [|lia]. destruct t, ch, r, e42, e62, ro; vm_compute; reflexivity.
Qed.

Lemma rm_B_ra_e42 : forall H mem F t ch r e e62 ro o n,
rl_fsh segs H mem F (rm_sh t ch r e true e62 ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_E42 + o) n.
Proof.
intros H mem F t ch r e e62 ro o n P HF Ho Hn. unfold RM_E42. change 0x180 with (8 * Z.of_nat 48).
apply (rm_fsh_ra_obj H mem F _ 48 13 0 o n P HF); [rewrite rm_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rm_nth_range _ 48 13); [|lia]. destruct t, ch, r, e, e62, ro; vm_compute; reflexivity.
Qed.

Lemma rm_B_ra_e62 : forall H mem F t ch r e e42 ro o n,
rl_fsh segs H mem F (rm_sh t ch r e e42 true ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_E62 + o) n.
Proof.
intros H mem F t ch r e e42 ro o n P HF Ho Hn. unfold RM_E62. change 0x210 with (8 * Z.of_nat 66).
apply (rm_fsh_ra_obj H mem F _ 66 13 0 o n P HF); [rewrite rm_sh_len; lia | | lia | lia | left; reflexivity].
intros g Hg. apply (rm_nth_range _ 66 13); [|lia]. destruct t, ch, r, e, e42, ro; vm_compute; reflexivity.
Qed.

(* r and ro = role: shadow byte 0x04, so each access passes on the check's slow path (its last offset in the
   granule < 4): r's two checks (pod.h:240 r[k] 0x80d20, pod.h:244 r[k-1-i] 0x80d74); role is the parse's out argument
   (a1 = F+0x2a0 at the call 0x821b0), whose 4 bytes the callee checks. *)
Lemma rm_B_ra_r : forall H mem F t ch e e42 e62 ro o n,
rl_fsh segs H mem F (rm_sh t ch true e e42 e62 ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 4 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_R + o) n.
Proof.
intros H mem F t ch e e42 e62 ro o n P HF Ho Hn. unfold RM_R. change 0xe0 with (8 * Z.of_nat 28).
apply (rm_fsh_ra_obj H mem F _ 28 1 4 o n P HF); [rewrite rm_sh_len; lia | | lia | lia | right; lia].
intros g Hg. apply (rm_nth_range _ 28 1); [|lia]. destruct t, ch, e, e42, e62, ro; vm_compute; reflexivity.
Qed.

Lemma rm_B_ra_role : forall H mem F t ch r e e42 e62 o n,
rl_fsh segs H mem F (rm_sh t ch r e e42 e62 true) -> F mod 8 = 0 -> 0 <= o -> o + n <= 4 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_ROLE + o) n.
Proof.
intros H mem F t ch r e e42 e62 o n P HF Ho Hn. unfold RM_ROLE. change 0x2a0 with (8 * Z.of_nat 84).
apply (rm_fsh_ra_obj H mem F _ 84 1 4 o n P HF); [rewrite rm_sh_len; lia | | lia | lia | right; lia].
intros g Hg. apply (rm_nth_range _ 84 1); [|lia]. destruct t, ch, r, e, e42, e62; vm_compute; reflexivity.
Qed.

(* The frame-shadow region's chunks: one `CVal 1 (SLit v)` per shadow byte, from shadow_addr F. *)
Definition rm_fsh_cs (pat : list Z) : list YP09.chunk :=
map (fun i => YP09.mkChunk (Z.of_nat i) (CVal 1 (SLit (nth i pat 0)))) (seq 0 (length pat)).

Lemma rm_fsh_chunks : forall E H mem F pat,
rl_fsh segs H mem F pat -> Forall (fun v => 0 <= v < 256) pat ->
Forall (YP09.chunk_ok segs E (mrestrict H mem) (shadow_addr F)) (rm_fsh_cs pat).
Proof.
intros E H mem F pat P R. apply Forall_forall. intros c Hc. unfold rm_fsh_cs in Hc.
apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
assert (Rv : 0 <= nth i pat 0 < 256) by (rewrite Forall_forall in R; apply R; apply nth_In; lia).
apply (chunk_ok_val segs E _ (shadow_addr F) (Z.of_nat i) 1 (SLit (nth i pat 0)) (nth i pat 0));
[reflexivity | cbn; lia | lia |].
apply (rm_aview_val1 H mem). rewrite (P (Z.of_nat i) ltac:(lia)), Nat2Z.id. reflexivity.
Qed.

Lemma rm_fsh_of_chunks : forall E H mem F pat,
Forall (YP09.chunk_ok segs E (mrestrict H mem) (shadow_addr F)) (rm_fsh_cs pat) ->
Forall (fun v => 0 <= v < 256) pat -> rl_fsh segs H mem F pat.
Proof.
intros E H mem F pat C R i Hi. rewrite Forall_forall in C.
assert (Hin : In (YP09.mkChunk (Z.of_nat (Z.to_nat i)) (CVal 1 (SLit (nth (Z.to_nat i) pat 0)))) (rm_fsh_cs pat)).
{ unfold rm_fsh_cs. apply in_map_iff. exists (Z.to_nat i). split; [reflexivity|]. apply in_seq. lia. }
pose proof (C _ Hin 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb1, Hb2. rewrite Z2Nat.id, Z.add_0_r in Hb2 by lia.
injection Hb1 as <-.
assert (Rv : 0 <= nth (Z.to_nat i) pat 0 < 256) by (rewrite Forall_forall in R; apply R; apply nth_In; lia).
unfold aview. rewrite Hb2. cbn [option_map]. f_equal.
unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.mul_0_r, Z.shiftr_0_r, unsigned_lit_small by lia.
rewrite rm_unsigned_byte. apply Z.mod_small. exact Rv.
Qed.

(* ================================== 7. the real frame's cells ================================== *)
Definition rm_slots (H : word -> bool) (mem : word -> option byte) (R : Z) (l : list (Z * Z)) : Prop :=
Forall (fun c => val_mem segs (mrestrict H mem) (R + fst c) 8 (snd c mod 2 ^ 64)) l.

Lemma rm_slots_kept : forall H mem H' mem' R l,
rm_slots H mem R l ->
(forall c, In c l -> forall i, 0 <= i < 8 -> aview segs H' mem' (R + fst c + i) = aview segs H mem (R + fst c + i)) ->
rm_slots H' mem' R l.
Proof.
intros H mem H' mem' R l P K. unfold rm_slots in *. rewrite Forall_forall in *. intros c Hc k Hk.
rewrite (mbyte_of_aview segs H H' mem mem') by (apply K; [exact Hc | lia]). exact (P c Hc k Hk).
Qed.

Lemma rm_slots_chunk : forall E H mem R l o v e,
rm_slots H mem R l -> In (o, v) l -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
YP09.chunk_ok segs E (mrestrict H mem) R (YP09.mkChunk o (CVal 8 e)).
Proof.
intros E H mem R l o v e P Hin He Hv. unfold rm_slots in P. rewrite Forall_forall in P.
pose proof (P _ Hin) as V. cbn [fst snd] in V. rewrite Z.mod_small in V by lia.
apply (chunk_ok_val segs E _ R o 8 e v He); [cbn; lia | lia | exact V].
Qed.

(* RPgBase's cut facts (rl_at / rl_cut) carried across a step, a store or a call: a register fact needs the register
   unchanged, a cell fact its 8 bytes unchanged. *)
Definition rm_keeps (H : word -> bool) (mem : word -> option byte) (H' : word -> bool) (mem' : word -> option byte)
(regs regs' : bvmap 5 word) (e : rl_env) (l : rl_loc) : Prop :=
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall i, 0 <= i < 8 -> aview segs H' mem' (rl_xv e b + o + i) = aview segs H mem (rl_xv e b + o + i)
end.

Lemma rm_at_kept : forall H mem H' mem' regs regs' e l v,
rl_at segs H mem regs e l v -> rm_keeps H mem H' mem' regs regs' e l -> rl_at segs H' mem' regs' e l v.
Proof.
intros H mem H' mem' regs regs' e [r|b o] v A K; cbn [rl_at rm_keeps] in *.
- rewrite K. exact A.
- intros k Hk. rewrite (mbyte_of_aview segs H H' mem mem') by (apply K; lia). exact (A k Hk).
Qed.

Lemma rm_cut_kept : forall H mem H' mem' regs regs' e L,
rl_cut segs H mem regs e L -> (forall f, In f L -> rm_keeps H mem H' mem' regs regs' e (fst f)) ->
rl_cut segs H' mem' regs' e L.
Proof.
intros H mem H' mem' regs regs' e L C K. unfold rl_cut in *. rewrite Forall_forall in *. intros f Hf.
exact (rm_at_kept _ _ _ _ _ _ _ _ _ (C f Hf) (K f Hf)).
Qed.

(* The same over a list of (location, value) facts (a cut fact list of the walk's sub-cut states unfolds to this). *)
Lemma rm_atl_kept : forall H mem H' mem' regs regs' e (L : list (rl_loc * Z)),
Forall (fun f => rl_at segs H mem regs e (fst f) (snd f)) L ->
(forall f, In f L -> rm_keeps H mem H' mem' regs regs' e (fst f)) ->
Forall (fun f => rl_at segs H' mem' regs' e (fst f) (snd f)) L.
Proof.
intros H mem H' mem' regs regs' e L C K. rewrite Forall_forall in *. intros f Hf.
exact (rm_at_kept _ _ _ _ _ _ _ _ _ (C f Hf) (K f Hf)).
Qed.

(* rm_keeps from what a step changed: Wr is the set of bytes it may write (a store: [a, a + n)); a register fact
   needs its register unchanged, a cell fact its 8 bytes outside Wr. *)
Lemma rm_keeps_of : forall (Wr : Z -> Prop) H mem H' mem' regs regs' e l,
(forall x, ~ Wr x -> aview segs H' mem' x = aview segs H mem x) ->
match l with
| LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
| LCell b o => forall i, 0 <= i < 8 -> ~ Wr (rl_xv e b + o + i)
end ->
rm_keeps H mem H' mem' regs regs' e l.
Proof. intros Wr H mem H' mem' regs regs' e [r|b o] K L; cbn [rm_keeps]; [exact L|]. intros i Hi. apply K, L, Hi. Qed.

(* rm_keeps across a call, from its post's memory clause (every byte outside the callee's stack [sp - T, sp) and
   outside E kept: RPgCSpec rl_post, YG0d's intrinsic and allocator posts) and aregs_preserved. *)
Lemma rm_keeps_call : forall (E : Z -> Prop) sp T H mem H' mem' regs regs' e l,
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp - T <= a < sp) -> ~ E a -> aview segs H' mem' a = aview segs H mem a) ->
aregs_preserved regs regs' ->
match l with
| LReg r => acallee_saved r
| LCell b o => forall i, 0 <= i < 8 ->
  0 <= rl_xv e b + o + i < 2 ^ 64 /\ ~ (sp - T <= rl_xv e b + o + i < sp) /\ ~ E (rl_xv e b + o + i)
end ->
rm_keeps H mem H' mem' regs regs' e l.
Proof.
intros E sp T H mem H' mem' regs regs' e [r|b o] K P L; cbn [rm_keeps].
- exact (P r L).
- intros i Hi. destruct (L i Hi) as (L1 & L2 & L3). exact (K _ L1 L2 L3).
Qed.

(* A real-frame cell written or read as two 4-byte halves and as one 8-byte value. Role B's R+0x178 is case 0's
   parts[0] (`sd a2,0x178(s1)` 0x80e20), then the flag := -1 (`sd a0,0x178(s1)` 0x823c4) and pod_nearest's out cell
   (a0 = R+0x178 at 0x824cc, read back by `ld a2,0x178(s1)` 0x824d8), so a cut holds it as one 8-byte cell
   (rl_at (LCell XR 0x178)); these lemmas go between that form and two 4-byte cells. *)
Lemma rm_shiftr_mod_low : forall x n m p, 0 <= m -> 0 <= p -> m + p <= n ->
Z.shiftr (x mod 2 ^ n) m mod 2 ^ p = Z.shiftr x m mod 2 ^ p.
Proof.
intros x n m p Hm Hp Hn. apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i p) as [Hl|Hg].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma rm_lb_lo : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (k < 4)%nat ->
le_byte (lo + 2 ^ 32 * hi) 8 k = le_byte lo 4 k.
Proof.
intros lo hi k Hl Hh Hk. unfold le_byte.
change (8 * Z.of_nat 8) with 64. change (8 * Z.of_nat 4) with 32.
assert (Hv : 0 <= lo + 2 ^ 32 * hi < 2 ^ 64).
{ first [lia | change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia]. }
rewrite (Z.mod_small (lo + 2 ^ 32 * hi)) by exact Hv. rewrite (Z.mod_small lo (2 ^ 32)) by exact Hl.
change 256 with (2 ^ 8).
rewrite <- (rm_shiftr_mod_low (lo + 2 ^ 32 * hi) 32) by lia.
f_equal. f_equal. replace (lo + 2 ^ 32 * hi) with (lo + hi * 2 ^ 32) by ring.
rewrite Z.mod_add by lia. apply Z.mod_small. exact Hl.
Qed.

Lemma rm_lb_hi : forall lo hi k, 0 <= lo < 2 ^ 32 -> 0 <= hi < 2 ^ 32 -> (4 <= k < 8)%nat ->
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

Lemma rm_ask_join : forall (M : word -> option byte) a v0 v1,
val_mem segs M a 4 (v0 mod 2 ^ 32) -> val_mem segs M (a + 4) 4 (v1 mod 2 ^ 32) ->
val_mem segs M a 8 (v0 mod 2 ^ 32 + 2 ^ 32 * (v1 mod 2 ^ 32)).
Proof.
intros M a v0 v1 V0 V1 k Hk.
pose proof (Z.mod_pos_bound v0 (2 ^ 32) ltac:(lia)) as B0. pose proof (Z.mod_pos_bound v1 (2 ^ 32) ltac:(lia)) as B1.
destruct (Nat.lt_ge_cases k 4) as [Hl|Hg].
- rewrite (V0 k Hl). f_equal. f_equal. exact (eq_sym (rm_lb_lo _ _ k B0 B1 Hl)).
- replace (a + Z.of_nat k) with (a + 4 + Z.of_nat (k - 4)) by lia.
  rewrite (V1 (k - 4)%nat ltac:(lia)). f_equal. f_equal. exact (eq_sym (rm_lb_hi _ _ k B0 B1 ltac:(lia))).
Qed.

Lemma rm_ask_split : forall (M : word -> option byte) a v0 v1,
val_mem segs M a 8 (v0 mod 2 ^ 32 + 2 ^ 32 * (v1 mod 2 ^ 32)) ->
val_mem segs M a 4 (v0 mod 2 ^ 32) /\ val_mem segs M (a + 4) 4 (v1 mod 2 ^ 32).
Proof.
intros M a v0 v1 V.
pose proof (Z.mod_pos_bound v0 (2 ^ 32) ltac:(lia)) as B0. pose proof (Z.mod_pos_bound v1 (2 ^ 32) ltac:(lia)) as B1.
split; intros k Hk.
- rewrite (V k ltac:(lia)). f_equal. f_equal. exact (rm_lb_lo _ _ k B0 B1 Hk).
- replace (a + 4 + Z.of_nat k) with (a + Z.of_nat (k + 4)) by lia.
  rewrite (V (k + 4)%nat ltac:(lia)). f_equal. f_equal.
  etransitivity; [exact (rm_lb_hi _ _ (k + 4) B0 B1 ltac:(lia)) |].
  replace (k + 4 - 4)%nat with k by lia. reflexivity.
Qed.

(* ========================= 9. the segment's start facts at the current memory =========================
   A cut inside a segment knows the start state's facts (rl_seg_pre, the input premises) and that every byte outside
   a write set Wr (rl_seg_post's kept clause: the callees' stack below R and the image's write ranges) is as at the
   start. These carry the input bytes, their shadow bytes, the shadow hull and rom_view to the current memory; the
   address facts after them show that the input's shadow bytes avoid each part of Wr. *)
Lemma rm_bytes_kept_wr : forall (Wr : Z -> Prop) H mem H' mem' a l,
rm_bytes H mem a l -> (forall x, ~ Wr x -> aview segs H' mem' x = aview segs H mem x) ->
(forall x, a <= x < a + Z.of_nat (length l) -> ~ Wr x) -> rm_bytes H' mem' a l.
Proof. intros Wr H mem H' mem' a l B K D. apply (rm_bytes_kept H mem); [exact B|]. intros x Hx. apply K, D, Hx. Qed.

Lemma rm_ra_kept : forall H mem H' mem' K a n,
range_addressable (aview segs H mem) K a n ->
(forall x, a <= x < a + n -> aview segs H' mem' (shadow_of_addr K x) = aview segs H mem (shadow_of_addr K x)) ->
range_addressable (aview segs H' mem') K a n.
Proof. intros H mem H' mem' K a n R E. exact (range_addressable_agree _ _ K a n E R). Qed.

Lemma rm_ra_kept_wr : forall (Wr : Z -> Prop) H mem H' mem' K a n,
range_addressable (aview segs H mem) K a n -> (forall x, ~ Wr x -> aview segs H' mem' x = aview segs H mem x) ->
(forall x, a <= x < a + n -> ~ Wr (shadow_of_addr K x)) -> range_addressable (aview segs H' mem') K a n.
Proof. intros Wr H mem H' mem' K a n R E D. apply (rm_ra_kept H mem); [exact R|]. intros x Hx. apply E, D, Hx. Qed.

Lemma rm_hull_kept : forall H mem H' mem' x n,
shadow_hull_vis (aview segs H mem) x n ->
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 ->
 aview segs H mem s <> None -> aview segs H' mem' s <> None) ->
shadow_hull_vis (aview segs H' mem') x n.
Proof. intros H mem H' mem' x n V P s Hs. exact (P s Hs (V s Hs)). Qed.

Lemma rm_rom_kept : forall (W W' : world segs) mem mem',
rom_view segs W mem -> (forall a, in_rom segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
rom_view segs W' mem'.
Proof. intros W W' mem mem' R K a Ha. rewrite K by exact Ha. exact (R a Ha). Qed.

Lemma rm_rom_kept_wr : forall (Wr : Z -> Prop) (W W' : world segs) mem mem',
rom_view segs W mem -> (forall a, ~ Wr a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
(forall a, in_rom segs a -> ~ Wr a) -> rom_view segs W' mem'.
Proof. intros Wr W W' mem mem' R K D. apply (rm_rom_kept W W' mem mem' R). intros a Ha. apply K, D, Ha. Qed.

(* An addressable range's shadow bytes are not the frame's poisoned ones: at one state, a shadow byte that some
   addressable byte reads is 0 or below 8, and every byte of a pattern like P0 is 0xf1 .. 0xf8. *)
Lemma rm_ra_not_fsh : forall H mem F pat a n,
range_addressable (aview segs H mem) SHADOW_OFF a n -> rl_fsh segs H mem F pat -> Forall (fun v => 8 <= v) pat ->
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
   stack, the real frame's cells). P0's bytes are all >= 8 (rm_ra_not_fsh's premise). *)
Lemma rm_shadow_band : forall x, 0 <= x < kHighMemEnd ->
kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighMemBeg.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kLowMemEnd, kHighMemBeg. unfold kHighMemEnd in Hx.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.
Section band. Context {rc : YM05.RunCeil}.
Lemma rm_shadow_not_app : forall x lo len, 0 <= x < kHighMemEnd -> in_app lo len ->
~ (lo <= shadow_of_addr SHADOW_OFF x < lo + len).
Proof.
intros x lo len Hx Ha Hin. pose proof (rm_shadow_band x Hx) as Hb.
unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg in *. lia.
Qed.
End band.
Lemma rm_shadow_not_high : forall x lo, 0 <= x < kHighMemEnd -> kHighMemBeg <= lo ->
~ (lo <= shadow_of_addr SHADOW_OFF x).
Proof. intros x lo Hx Hl Hin. pose proof (rm_shadow_band x Hx). lia. Qed.
Lemma rm_sh_P0_big : Forall (fun v => 8 <= v) (hi_shA role_himg_B).
Proof. rewrite <- rm_sh_P0. cbv [rm_sh repeat app]. repeat constructor; lia. Qed.

(* ============================ 8. risk 2 at its concrete site, 0x8028c (E01, data[0]) ============================
   The code, read from image B's loaded segments: 0x80284 srli a0,s5,3; 0x80288 add a0,a0,s11; 0x8028c lb a0,0(a0);
   0x80290 beqz a0,+8; 0x80294 j 0x8264c; 0x80298 lbu a0,0(s5); and 0x8264c andi a1,s5,7; 0x82650 bge a1,a0,+8;
   0x82654 j 0x80298; 0x82658 mv a0,s5 (the error-path call follows). s5 is the input pointer p, s11 the shadow
   offset. The trap guard before it (0x80274 addi s4,s5,1; li a0,1; bltu a0,s4,+8; j 0x82604) is its own step.
   rm_B_tok_none: the engine's slow-block recognizer (YCbn.slow_block) fails at the `beqz`'s fall-through 0x80294
   (a `j`, decoded, not an `andi`), so tok_branch takes its None arm (shadow 0 over the whole granule); rm_B_slow_ok:
   the out-of-line block 0x8264c itself has the shape the recognizer accepts. rm_B_8028c_gran: for an input of
   1 .. 7 bytes that obligation is false at data[0]; rm_B_8028c_cell: the shadow cell the route loads instead, and why
   its error-path arm is dead. Four more sites have this shape (0x802f8, 0x80350, 0x8078c, 0x80b18: the `bge; j back`
   slow block) and differ in registers and in the cursor; 0x8078c's cursor has no alignment fact (rm_B_8078c_step
   below). *)
Definition rm_B_tbl8028c : ctable := build_table rsegs 0x80284 6 (build_table rsegs 0x8264c 4 TEmpty).
Lemma rm_B_tbl8028c_ok : table_ok rsegs rm_B_tbl8028c.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

Lemma rm_B_tok_none : forall t, YCbn.slow_block rm_B_tbl8028c 0x80294 0x80298 t = None.
Proof. intros t. vm_compute. reflexivity. Qed.
Lemma rm_B_tok_arm :
match YCbn.dec rm_B_tbl8028c 0x80294 with
| Some i => match YCbn.as_andi i with Some _ => false | None => true end
| None => false end = true /\
YCbn.decp rm_B_tbl8028c YCbn.as_j 0x80294 = Some (0x8264c - 0x80294) /\
match YCbn.decp rm_B_tbl8028c YCbn.as_branch 0x80290 with
| Some (c, r1, r2, off) =>
  match c with BC_EQ => (bv_unsigned r1 =? 10) && (bv_unsigned r2 =? 0) && (off =? 8) | _ => false end
| None => false end = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rm_B_slow_ok :
match YCbn.slow_block rm_B_tbl8028c 0x8264c 0x80298 (Z_to_bv 5 10) with
| Some (u, xr, k) => (bv_unsigned u =? 11) && (bv_unsigned xr =? 21) && (k =? 0)
| None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Section site. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Lemma rm_B_8028c_gran : forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n < 8 ->
~ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 8.
Proof.
intros ly S W mem md p n HAR Hin Hn.
destruct (al_shadow _ _ (AR_laws_ok segs B) ly S W mem md p n HAR Hin) as [Hbs _].
unfold req_size in Hbs. replace (n =? 0) with false in Hbs by (symmetry; apply Z.eqb_neq; lia).
exact (rm_ra_gran_false _ _ p n Hbs Hn).
Qed.
Lemma rm_B_8028c_cell : forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
exists s, aview segs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some s /\ saddr_ok p s /\
(s <> 0 -> 0 < s < 8 /\ p mod 8 < s).
Proof.
intros ly S W mem md p n HAR Hin Hn.
assert (Hrq : 1 <= req_size n) by (unfold req_size; destruct (n =? 0); lia).
destruct (rm_blk_ra segs B ly S W mem md p n p 1 HAR Hin ltac:(lia) ltac:(lia)) as [R _].
destruct (rm_ra_cell _ _ _ R) as (s & Hs & Hok). exists s. split; [exact Hs|]. split; [exact Hok|].
intros Hs0. exact (rm_ra_slow p s Hok Hs0).
Qed.
End site.

(* ---- the region route through the symbolic engine at 0x8028c ----
   The input's metadata byte s (at shadow_of_addr SHADOW_OFF p, p = s5) is a one-byte region of the symbolic state,
   based on an extra atom (32) whose value is that address; a second extra atom (33) is the byte. The facts: atom 21
   (s5 = p) 8-aligned, atom 33 in [0, 7] (so the `lb` keeps the plain atom), and the alias ((s5 >> 3) + s11, atom 32).
   The `add` 0x80288 rewrites a0 to atom 32 by the alias (YP0e.s_alu2), the `lb` is a plain region load, and no
   shadow obligation is raised. The engine stops at the `beqz` 0x80290 (a0 = atom 33 against 0) and at the slow
   block's `bge` 0x82650 (a1 = p & 7 = 0 by p's alignment, against atom 33); the branch split takes each outcome; the
   error arm (0 >= s with s <> 0) dies by saddr_ok. The same state without the region makes the token path ask
   shadow 0 over p's whole granule (rm_B_8028c_gran: false for an input of 1 .. 7 bytes). A walk lane uses the route
   mid-run by adding the region, the alias fact keyed on the atoms of the registers holding p and SHADOW_OFF, and the
   byte's atom fact to its symbolic state; without p's alignment fact the `andi` stays p & 7 and the error arm needs
   YCbn.alu_and7 and the p mod 8 < s form of saddr_ok (rm_B_8078c_step below does exactly that). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK0h YK0i YK1b YK1a.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0e YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI08 YA0o YCbm YA0q YI16.

Lemma rm_B_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* s11 (x27) holds SHADOW_OFF, so the shadow base is its own atom; no block shadow entry is used. *)
Definition RM_B_Bx : sv := SOff 27 0.
Definition RM_B_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* atom 21 = s5 = p (8-aligned, in the allocator's range); atom 33 = the metadata byte, in [0, 7];
   atom 32 = the address of that byte, declared equal to (s5 >> 3) + s11 *)
Definition rm_B_r_facts : facts :=
  mkFacts [(21%nat, mkAF 4096 0x800000000000 3); (33%nat, mkAF 0 7 0)] []
          [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) (SOff 27 0), SOff 32 0)].
Definition rm_B_r_mem : smem := [YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]].
Definition rm_B_r_ss : sstate := mkSS 0x80284 sr_atoms rm_B_r_mem None rm_B_r_facts.
(* the registers the two live arms keep, at both sites: all but a0 (x10) and a1 (x11) *)
Definition RM_B_KEEP : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.

Section route. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* Every register but a0 and a1 holds its entry value when the symbolic state keeps it as its own atom. *)
Lemma rm_B_keep_regs : forall E ss ms regs extra,
st_ok rsegs E ss ms -> env_agree 32 (Ereg regs extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) RM_B_KEEP = true ->
forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs extra HS HA Hf r H10 H11.
destruct (Z.eq_dec (bv_unsigned r) 0) as [Hr0 | Hr0].
{ assert (Er : r = (0%bv : bv 5)) by (apply bv_eq; rewrite Hr0; vm_compute; reflexivity).
  subst r. unfold getr. rewrite bv_eqb_refl. reflexivity. }
apply (regs_kept_of_st_ok rsegs E ss ms regs extra RM_B_KEEP HS HA Hf r).
pose proof (u5_range r) as Hu.
rewrite <- (Z_to_bv_bv_unsigned 5 r).
assert (Hc : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/
bv_unsigned r = 5 \/ bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/
bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/ bv_unsigned r = 16 \/
bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/ bv_unsigned r = 21 \/
bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/ bv_unsigned r = 26 \/
bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/ bv_unsigned r = 31) by lia.
repeat match goal with Hd : _ \/ _ |- _ => destruct Hd as [Hd|Hd] end;
rewrite Hc; cbv [RM_B_KEEP]; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

(* The walk reaches 0x80298, the load of the input byte, with every register but a0 and a1 as at 0x80284, the same
   memory and the same model up to materialization; no premise asks the granule's other bytes to be addressable. *)
Lemma rm_B_8028c_step : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) p s,
getr regs (Z_to_bv 5 21) = w64 p ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
p mod 8 = 0 -> 4096 <= p -> p + 8 <= kHighMemEnd ->
aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF p) = Some s ->
saddr_ok p s ->
(forall regs' md',
   (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr regs' r = getr regs r) ->
   same_but_materialized md md' ->
   SRr rsegs W (cfg_at rsegs 0x80298 regs' mem md') Q) ->
SRr rsegs W (cfg_at rsegs 0x80284 regs mem md) Q.
Proof.
intros W regs mem md Q p s H21 H27 Hal Hlo Hhi Hav Hok K.
pose proof rm_B_wx as Hwx.
pose proof (rm_sok_range p s Hal Hok) as Hs7.
unfold kHighMemEnd in Hhi.
set (extra := [Z_to_bv 64 (shadow_of_addr SHADOW_OFF p); Z_to_bv 64 s]).
set (E := Ereg regs extra).
assert (Ew21 : ew E 21%nat = Z_to_bv 64 p).
{ unfold E. rewrite (ew_Ereg_nat regs extra 21%nat (Z_to_bv 5 21) eq_refl), H21. reflexivity. }
assert (Ew27 : ew E 27%nat = Z_to_bv 64 SHADOW_OFF).
{ unfold E. rewrite (ew_Ereg_nat regs extra 27%nat (Z_to_bv 5 27) eq_refl), H27. reflexivity. }
assert (Ew32 : ew E 32%nat = Z_to_bv 64 (SHADOW_OFF + p / 8)) by reflexivity.
assert (Ew33 : ew E 33%nat = Z_to_bv 64 s) by reflexivity.
assert (HG : facts_ok E rm_B_r_facts).
{ unfold facts_ok. split; [|split].
  - cbv [rm_B_r_facts f_atoms]. cbn [atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew21, unsigned_lit_small by lia.
      change (2 ^ 3) with 8. lia.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, unsigned_lit_small by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  - exact I.
  - cbv [rm_B_r_facts f_alias]. cbn [alias_ok]. split; [|exact I].
    exact (shadow_decl_ok E 21%nat 27%nat 32%nat p SHADOW_OFF Ew21 ltac:(lia) Ew27 Ew32). }
assert (HS : st_ok rsegs E rm_B_r_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80284) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rm_cell_region rsegs E (w_H W) mem 32%nat (SHADOW_OFF + p / 8) s (SOff 33 0)).
    + rewrite Ew32. apply unsigned_lit_small. unfold SHADOW_OFF. split; [lia|].
      assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). lia.
    + unfold shadow_of_addr in Hav. exact Hav.
    + cbn [sv_denot]. rewrite Ew33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    + unfold SHADOW_OFF. lia.
    + unfold SHADOW_OFF. assert (p / 8 <= p) by (apply Z.div_le_upper_bound; lia). lia.
  - cbv [rm_B_r_ss rm_B_r_mem]. cbn [ss_mem pairwise_disjoint all_disjoint]. split; exact I.
  - exact HG. }
assert (SHOK : sh_ok rsegs RM_B_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs extra) E) by apply env_agree_refl.
unfold cfg_at. change (w64 0x80284) with (Z_to_bv 64 0x80284).
(* 0x80284 .. 0x8028c, the region load, then the `beqz` *)
srr_run_tok rm_B_tbl8028c_ok HS SHOK RM_B_span.
assert (Em1 : ms_mem ms = mem)
  by (apply (frame_of_read_only E (ss_mem rm_B_r_ss) mem (ms_mem ms)); [vm_compute; reflexivity | exact HF]).
srr_branch_tok rm_B_tbl8028c_ok HS SHOK RM_B_span.
- (* the byte is 0: the check passes at once *)
  srr_run_to_tok rm_B_tbl8028c_ok HS SHOK RM_B_span 0x80298.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms0 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems, Em2. apply K.
  + apply (rm_B_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
  + apply with_vm_backing_same.
- (* the byte is not 0: the slow block, then its `bge` *)
  assert (Hs0 : s <> 0).
  { intros Hz. cbn [sv_denot] in Hc. rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc by lia.
    rewrite Hz in Hc. vm_compute in Hc. discriminate. }
  pose proof (rm_sok_pos p s Hal Hok Hs0) as Hspos.
  srr_run_tok rm_B_tbl8028c_ok HS SHOK RM_B_span.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  srr_branch_tok rm_B_tbl8028c_ok HS SHOK RM_B_span.
  + (* the error path: p mod 8 >= the byte, which saddr_ok refuses *)
    exfalso. cbv [branch_taken] in Hc0. cbn [sv_denot] in Hc0.
    rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc0 by lia.
    rewrite YCbn.bv_lts_small in Hc0 by lia.
    apply negb_true_iff in Hc0. apply Z.ltb_nlt in Hc0. lia.
  + (* the check passes: back to 0x80298 *)
    srr_run_to_tok rm_B_tbl8028c_ok HS SHOK RM_B_span 0x80298.
    assert (Em3 : ms_mem ms1 = mem)
      by (rewrite <- Em2; refine (frame_of_read_only E _ _ _ _ HF1); vm_compute; reflexivity).
    pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms1 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    rewrite Ems, Em3. apply K.
    * apply (rm_B_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
    * apply with_vm_backing_same.
Qed.
End route.

(* ================= 8b. risk 2 with a cursor of unknown alignment, at 0x8078c (P.sel, the property key byte) =========
   The code, read from image B's loaded segments: 0x80784 srli a0,s4,3; 0x80788 add a0,a0,s11; 0x8078c lb a0,0(a0);
   0x80790 beqz a0,+8; 0x80794 j 0x81da0; 0x80798 lbu a1,0(s4); and the out-of-line block 0x81da0 andi a1,s4,7;
   0x81da4 bge a1,a0,0x82960 (the error-path call: mv a0,s4; jal errpath_load1); 0x81da8 j 0x80798. s4 is the cursor
   x (in.p, after the flags byte and the property bytes: no alignment fact), s11 the shadow offset. The slow block is
   the `bge; j back` form YCbn.slow_block accepts (rm_B_slow8078c_ok), but the token path meets the `beqz`'s
   fall-through `j` first (rm_B_tok8078c_none) and asks shadow 0 over x's whole granule, false when x is in the
   input's partial last granule; the region route covers it. The `andi` stays x & 7 (YCbn.alu_and7) and saddr_ok's
   x mod 8 < s kills the error-path arm. *)
Definition rm_B_tbl8078c : ctable := build_table rsegs 0x80784 6 (build_table rsegs 0x81da0 3 TEmpty).
Lemma rm_B_tbl8078c_ok : table_ok rsegs rm_B_tbl8078c.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

Lemma rm_B_tok8078c_none : forall t, YCbn.slow_block rm_B_tbl8078c 0x80794 0x80798 t = None.
Proof. intros t. vm_compute. reflexivity. Qed.
Lemma rm_B_slow8078c_ok :
match YCbn.slow_block rm_B_tbl8078c 0x81da0 0x80798 (Z_to_bv 5 10) with
| Some (u, xr, k) => (bv_unsigned u =? 11) && (bv_unsigned xr =? 20) && (k =? 0)
| None => false end = true.
Proof. vm_compute. reflexivity. Qed.

(* atom 20 = s4 = x (in the allocator's range, no alignment); atom 33 = the metadata byte, in [0, 7]; atom 32 = the
   address of that byte, declared equal to (s4 >> 3) + s11 *)
Definition rm_B_f_facts : facts :=
  mkFacts [(20%nat, mkAF 4096 0x800000000000 0); (33%nat, mkAF 0 7 0)] []
          [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 20 0) (SLit 3)) (SOff 27 0), SOff 32 0)].
Definition rm_B_f_ss : sstate := mkSS 0x80784 sr_atoms rm_B_r_mem None rm_B_f_facts.

Section route8078c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* The walk reaches 0x80798, the load of the key byte, with every register but a0 and a1 as at 0x80784, the same
   memory and the same model up to materialization. The shadow byte and saddr_ok come from the input's
   range_addressable (rm_in_ra, rm_ra_cell) at x = src + c, c < left. *)
Lemma rm_B_8078c_step : forall (W : world rsegs) regs mem md (Q : world rsegs -> config -> Prop) x s,
getr regs (Z_to_bv 5 20) = w64 x ->
getr regs (Z_to_bv 5 27) = w64 SHADOW_OFF ->
4096 <= x -> x + 8 <= kHighMemEnd ->
aview rsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x) = Some s ->
saddr_ok x s ->
(forall regs' md',
   (forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> getr regs' r = getr regs r) ->
   same_but_materialized md md' ->
   SRr rsegs W (cfg_at rsegs 0x80798 regs' mem md') Q) ->
SRr rsegs W (cfg_at rsegs 0x80784 regs mem md) Q.
Proof.
intros W regs mem md Q x s H20 H27 Hlo Hhi Hav Hok K.
pose proof rm_B_wx as Hwx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hx8.
assert (Hs7 : 0 <= s <= 7) by (destruct Hok as [-> | [H1 H2]]; lia).
unfold kHighMemEnd in Hhi.
set (extra := [Z_to_bv 64 (shadow_of_addr SHADOW_OFF x); Z_to_bv 64 s]).
set (E := Ereg regs extra).
assert (Ew20 : ew E 20%nat = Z_to_bv 64 x).
{ unfold E. rewrite (ew_Ereg_nat regs extra 20%nat (Z_to_bv 5 20) eq_refl), H20. reflexivity. }
assert (Ew27 : ew E 27%nat = Z_to_bv 64 SHADOW_OFF).
{ unfold E. rewrite (ew_Ereg_nat regs extra 27%nat (Z_to_bv 5 27) eq_refl), H27. reflexivity. }
assert (Ew32 : ew E 32%nat = Z_to_bv 64 (SHADOW_OFF + x / 8)) by reflexivity.
assert (Ew33 : ew E 33%nat = Z_to_bv 64 s) by reflexivity.
assert (HG : facts_ok E rm_B_f_facts).
{ unfold facts_ok. split; [|split].
  - cbv [rm_B_f_facts f_atoms]. cbn [atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew20, unsigned_lit_small by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Ew33, unsigned_lit_small by lia.
      change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
  - exact I.
  - cbv [rm_B_f_facts f_alias]. cbn [alias_ok]. split; [|exact I].
    exact (shadow_decl_ok E 20%nat 27%nat 32%nat x SHADOW_OFF Ew20 ltac:(lia) Ew27 Ew32). }
assert (HS : st_ok rsegs E rm_B_f_ss (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80784) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (rm_cell_region rsegs E (w_H W) mem 32%nat (SHADOW_OFF + x / 8) s (SOff 33 0)).
    + rewrite Ew32. apply unsigned_lit_small. unfold SHADOW_OFF. split; [lia|].
      assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
    + unfold shadow_of_addr in Hav. exact Hav.
    + cbn [sv_denot]. rewrite Ew33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    + unfold SHADOW_OFF. lia.
    + unfold SHADOW_OFF. assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
  - cbv [rm_B_f_ss rm_B_r_mem]. cbn [ss_mem pairwise_disjoint all_disjoint]. split; exact I.
  - exact HG. }
assert (SHOK : sh_ok rsegs RM_B_Bx [] E (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HAE : env_agree 32 (Ereg regs extra) E) by apply env_agree_refl.
unfold cfg_at. change (w64 0x80784) with (Z_to_bv 64 0x80784).
(* 0x80784 .. 0x8078c, the region load, then the `beqz` *)
srr_run_tok rm_B_tbl8078c_ok HS SHOK RM_B_span.
assert (Em1 : ms_mem ms = mem)
  by (apply (frame_of_read_only E (ss_mem rm_B_f_ss) mem (ms_mem ms)); [vm_compute; reflexivity | exact HF]).
srr_branch_tok rm_B_tbl8078c_ok HS SHOK RM_B_span.
- (* the byte is 0: the check passes at once *)
  srr_run_to_tok rm_B_tbl8078c_ok HS SHOK RM_B_span 0x80798.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms0 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
  rewrite Ems, Em2. apply K.
  + apply (rm_B_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
  + apply with_vm_backing_same.
- (* the byte is not 0: 0x80794 j 0x81da0, the `andi`, then the `bge` *)
  assert (Hs0 : s <> 0).
  { intros Hz. cbn [sv_denot] in Hc. rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc by lia.
    rewrite Hz in Hc. vm_compute in Hc. discriminate. }
  srr_run_tok rm_B_tbl8078c_ok HS SHOK RM_B_span.
  assert (Em2 : ms_mem ms0 = mem)
    by (rewrite <- Em1; refine (frame_of_read_only E _ _ _ _ HF0); vm_compute; reflexivity).
  srr_branch_tok rm_B_tbl8078c_ok HS SHOK RM_B_span.
  + (* the error path 0x82960: x mod 8 >= the byte, which saddr_ok refuses *)
    exfalso.
    assert (G : sv_denot E (SAlu ALU_AND (SOff 20 0) (SLit 7)) = Z_to_bv 64 (x mod 8)).
    { cbn [sv_denot]. rewrite Ew20, unsigned_lit_small, Z.add_0_r by lia. apply alu_and7. unfold M64. lia. }
    rewrite G in Hc0. cbn [sv_denot] in Hc0. rewrite Ew33, Z.add_0_r, unsigned_lit_small in Hc0 by lia.
    cbv [branch_taken] in Hc0. rewrite (rm_ra_slow_bv x s Hok Hs0) in Hc0. cbn [negb] in Hc0. discriminate Hc0.
  + (* x mod 8 < s: 0x81da8 j 0x80798, the check passes *)
    srr_run_to_tok rm_B_tbl8078c_ok HS SHOK RM_B_span 0x80798.
    assert (Em3 : ms_mem ms1 = mem)
      by (rewrite <- Em2; refine (frame_of_read_only E _ _ _ _ HF1); vm_compute; reflexivity).
    pose proof (st_ok_restrict_mkst rsegs (w_H W) E _ ms1 HS eq_refl) as Ems. cbn [ss_pc] in Ems.
    rewrite Ems, Em3. apply K.
    * apply (rm_B_keep_regs E _ _ regs extra HS HAE). vm_compute. reflexivity.
    * apply with_vm_backing_same.
Qed.
End route8078c.
