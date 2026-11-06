(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; addresses measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the memory and shadow layer of the walk of
   LLVMFuzzerTestOneInput (0x7ff88). Proves no function (kind: segment lemma). Every lemma is over the concrete state
   (aview, val_mem, garr8, the shadow bytes), generic in the segments segs, so that each walk piece can rebuild its
   symbolic regions from a cut's facts and give the facts back after its run, a store or a call.

   1. Byte lists: the little-endian value of a byte list and its bytes (le_byte), the bytes of Z_to_le_bytes.
   2. rm_bytes: a list of bytes at an address, the form of role_build_contract's and role_check_contract's garr8
      premises (pp's image, the input after the flags byte); kept, split, slice, patch (a store or a call's write
      inside the list), the value of a field, the bytes a store leaves; the fields of pp's image (len, is_props,
      has_params, params_struct, ent[i], n_ent, corrupt, buf) as the code loads them; read-only image bytes.
   3. Calls: what __asan_memset / __asan_memcpy leave (the memory part of YG0d.aintrin_realizes' post); the shadow
      premises of a block's bytes (pp, pod, the input).
   4. Shadow checks. The engine's token path (lib/Reusable/YCbn.v tok_branch) follows a check's slow block only when
      it starts at the `bnez` target or at the `beqz` fall-through. Measured over the 146 instrumented checks of
      LLVMFuzzerTestOneInput (capstone over the unstripped twin; the branch after each shadow load, and the slow block
      it reaches): 66 are `bnez t,L` with L = `andi u,x,7; [addi u,u,k]; blt u,t,back` (the token path takes both
      outcomes), 30 are `beqz t,+8; j L` with L = `andi u,x,7; bge u,t,report; j back`, 37 are `beqz t,+8; j report`
      and 13 are `bnez t,report` (no slow block: 8-byte accesses and full-granule 4-byte fields). For the `beqz; j`
      forms the token path takes its None arm, which asks shadow 0 over the whole granule. That holds for every check
      except five input reads whose granule can be the input's last, partial one: 0x80158 (E01, data[0]; for
      1 <= n <= 7 the shadow byte of p is n), 0x801bc, 0x80208, 0x80600, 0x80a38. There the walk puts the input's
      shadow cell in a region (rm_cell_region) and loads it as memory, not through the token path: the engine's
      sym_step_sh reaches it by shadow_norm when the cursor is an 8-aligned atom plus a literal offset (data[0]); for a
      cursor atom of unknown alignment the walk pins the shadow-address register to a fresh atom holding that address
      (the region's base) before the `lb`. It then splits the `beqz` and the slow block's `bge`; rm_ra_cell /
      rm_ra_slow(_bv) kill the report arm. rm_ra_gran_false records why the token path's obligation cannot be paid
      there; section 8 checks the code and the facts at 0x80158.
   5. The stack's zero shadow: the real-frame cells the code shadow-checks (R+0x118, R+0x120: the store8 check of
      parts[1] at 0x80d70 and pod_nearest's out) from AR's zero-shadow ranges.
   6. The frame for locals F (class 3, 512 bytes, 52 shadow bytes from shadow_addr F): t F+0x20 (96 bytes), ch F+0xa0
      (24), r F+0xe0 (4), e F+0xf0 (104), role F+0x180 (4). rm_sh gives its shadow bytes in each scope state (the
      prologue's 52 stores 0x8006c-0x8013c, and the twelve scope-store sites: t 0x80b40 / 0x80bac (in), ch 0x80bf4 /
      0x8138c (in), r 0x80c0c (in) / 0x80d10 (out), t and ch 0x80e18-0x80e50 (out), e 0x80a84 (in) / 0x81858 / 0x81c98
      (out), role 0x820ec (in) / 0x8248c (out)); the checks on t, ch, r, e and role (r's two accesses see the shadow
      byte 0x04 and pass on the slow path); the frame-shadow region's chunks.
   7. The real frame's 8-byte cells (R = s1) and RPgBase's cut facts (rl_at / rl_cut): kept across a step, a store
      or a call, and as engine chunks.
   8. Risk 2 at 0x80158, on image A's code (Img0.rsegs).
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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Model.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec RPgImgA.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Img0.
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

(* Read-only data the code loads without a check or after one (the tables ints / floats / t / t.9 / s in .rodata,
   vocab / odd_ch / param in .data.rel.ro, the jump table at 0x20e94): the image's bytes, by the harness pre's
   arodata_okP (RPgBase; rl_seg_pre carries it), as rm_bytes of the list l the segments hold there. *)
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
   (the five `beqz t,+8; j L` input reads), or any other read-only byte. *)
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

(* The real-frame cells image A shadow-checks (hi_rz: [R+0x118, R+0x128)): the store8 check of parts[1] at R+0x120
   (0x80d70) and pod_nearest's out at R+0x118. R + 0x1a0 <= h: the real frame lies below the entry sp. *)
Lemma rm_A_rz : forall ly S W mem md R h,
AR segs B ly S W mem md -> ly_stk_lo ly <= R -> R + 0x1a0 <= h -> h <= ly_stk_hi ly -> h mod 8 = 0 ->
Forall (fun z => range_addressable (aview segs (w_H W) mem) SHADOW_OFF (R + fst z) (snd z)) (hi_rz role_himg_A).
Proof.
intros ly S W mem md R h HAR Hlo Hh Hhi H8. cbn [hi_rz role_himg_A]. constructor; [|constructor].
cbn [fst snd]. apply (rm_stk_ra ly S W mem md _ _ h HAR); lia.
Qed.
End stk.

(* ================================ 6. the frame for locals (image A) ================================ *)
Definition RM_T : Z := 0x20.
Definition RM_CH : Z := 0xa0.
Definition RM_R : Z := 0xe0.
Definition RM_E : Z := 0xf0.
Definition RM_ROLE : Z := 0x180.

(* The 52 shadow bytes of F in a scope state: t (granules 0x04-0x0f), ch (0x14-0x16), e (0x1e-0x2a) are 0x00 in
   scope; r (0x1c) and role (0x30) are 0x04 (4 bytes usable); out of scope 0xf8; the guards 0xf1 / 0xf2 / 0xf3. *)
Definition rm_sh (t ch r e role : bool) : list Z :=
repeat 0xf1 4 ++ repeat (if t then 0 else 0xf8) 12 ++ repeat 0xf2 4 ++ repeat (if ch then 0 else 0xf8) 3 ++
repeat 0xf2 5 ++ [if r then 4 else 0xf8] ++ [0xf2] ++ repeat (if e then 0 else 0xf8) 13 ++ repeat 0xf2 5 ++
[if role then 4 else 0xf8] ++ repeat 0xf3 3.

Lemma rm_sh_P0 : rm_sh false false false false false = role_A_shA.
Proof. vm_compute. reflexivity. Qed.
Lemma rm_sh_PB : rm_sh false false false false true = role_A_shB.
Proof. vm_compute. reflexivity. Qed.
Lemma rm_sh_len : forall t ch r e ro, length (rm_sh t ch r e ro) = 52%nat.
Proof. intros [] [] [] [] []; reflexivity. Qed.
Lemma rm_sh_bytes : forall t ch r e ro, Forall (fun v => 0 <= v < 256) (rm_sh t ch r e ro).
Proof.
intros t ch r e ro. apply Forall_forall. intros v Hv.
destruct t, ch, r, e, ro; cbn in Hv; repeat (destruct Hv as [<-|Hv]; [lia|]); contradiction.
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

(* the twelve scope-store sites, as patterns *)
Lemma rm_sh_t_in : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 4 12 0 = rm_sh true ch r e ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_t_out : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 4 12 0xf8 = rm_sh false ch r e ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_ch_in : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 20 3 0 = rm_sh t true r e ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_ch_out : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 20 3 0xf8 = rm_sh t false r e ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_r_in : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 28 1 4 = rm_sh t ch true e ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_r_out : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 28 1 0xf8 = rm_sh t ch false e ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e_in : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 30 13 0 = rm_sh t ch r true ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_e_out : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 30 13 0xf8 = rm_sh t ch r false ro.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_role_in : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 48 1 4 = rm_sh t ch r e true.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.
Lemma rm_sh_role_out : forall t ch r e ro, rm_setn (rm_sh t ch r e ro) 48 1 0xf8 = rm_sh t ch r e false.
Proof. intros [] [] [] [] []; vm_compute; reflexivity. Qed.

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

(* The checks and the calls on the frame objects: each in-scope object's bytes are addressable. *)
Ltac rm_obj_ra P HF g0 len v :=
  apply (rm_fsh_ra _ _ _ _ _ _ P HF); [lia | rewrite rm_sh_len; lia |];
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  lazymatch goal with |- saddr_ok _ (nth ?ix ?pat 0) =>
  let Hg := fresh "Hg" in
  assert (Hg : nth ix pat 0 = v)
    by (apply (rm_nth_range pat g0 len v); [vm_compute; reflexivity | split;
        [apply Nat2Z.inj_le; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_le_lower_bound; lia
        | apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_lt_upper_bound; lia]]);
  rewrite Hg end.

Lemma rm_A_ra_t : forall H mem F ch r e ro o n,
rl_fsh segs H mem F (rm_sh true ch r e ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 96 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_T + o) n.
Proof.
intros H mem F ch r e ro o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold RM_T.
destruct ch, r, e, ro; rm_obj_ra P HF 4%nat 12%nat 0; left; reflexivity.
Qed.

Lemma rm_A_ra_ch : forall H mem F t r e ro o n,
rl_fsh segs H mem F (rm_sh t true r e ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 24 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_CH + o) n.
Proof.
intros H mem F t r e ro o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold RM_CH.
destruct t, r, e, ro; rm_obj_ra P HF 20%nat 3%nat 0; left; reflexivity.
Qed.

Lemma rm_A_ra_e : forall H mem F t ch r ro o n,
rl_fsh segs H mem F (rm_sh t ch r true ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 104 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_E + o) n.
Proof.
intros H mem F t ch r ro o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold RM_E.
destruct t, ch, r, ro; rm_obj_ra P HF 30%nat 13%nat 0; left; reflexivity.
Qed.

(* r and role: shadow byte 0x04, so each access passes on the check's slow path (offset in granule < 4). *)
Lemma rm_A_ra_r : forall H mem F t ch e ro o n,
rl_fsh segs H mem F (rm_sh t ch true e ro) -> F mod 8 = 0 -> 0 <= o -> o + n <= 4 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_R + o) n.
Proof.
intros H mem F t ch e ro o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold RM_R.
destruct t, ch, e, ro; rm_obj_ra P HF 28%nat 1%nat 4; right;
(split; [|lia]); replace i with (224 + (i - 224)) by lia; rewrite Z.add_mod, Z.mod_small with (a := i - 224) by lia;
change (224 mod 8) with 0; rewrite Z.add_0_l, Z.mod_small; lia.
Qed.

Lemma rm_A_ra_role : forall H mem F t ch r e o n,
rl_fsh segs H mem F (rm_sh t ch r e true) -> F mod 8 = 0 -> 0 <= o -> o + n <= 4 ->
range_addressable (aview segs H mem) SHADOW_OFF (F + RM_ROLE + o) n.
Proof.
intros H mem F t ch r e o n P HF Ho Hn. rewrite <- Z.add_assoc. unfold RM_ROLE.
destruct t, ch, r, e; rm_obj_ra P HF 48%nat 1%nat 4; right;
(split; [|lia]); replace i with (384 + (i - 384)) by lia; rewrite Z.add_mod, Z.mod_small with (a := i - 384) by lia;
change (384 mod 8) with 0; rewrite Z.add_0_l, Z.mod_small; lia.
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

(* The same over a list of (location, value) facts (RPgSeg's rs_at unfolds to this Forall). *)
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
Lemma rm_sh_P0_big : Forall (fun v => 8 <= v) role_A_shA.
Proof. repeat constructor; lia. Qed.

(* ============================ 8. risk 2 at its concrete site, 0x80158 (E01, data[0]) ============================
   The code, read from image A's loaded segments: 0x80150 srli a0,a2,3; 0x80154 add a0,a0,s7; 0x80158 lb a0,0(a0);
   0x8015c beqz a0,+8; 0x80160 j 0x82610; 0x80164 lbu a0,0(a2); and 0x82610 andi a1,a2,7; 0x82614 bge a1,a0,+8;
   0x82618 j 0x80164; 0x8261c mv a0,a2 (the report call follows). rm_A_tok_none: the engine's slow-block recognizer
   (YCbn.slow_block) fails at the `beqz`'s fall-through 0x80160 (a `j`, decoded, not an `andi`), so tok_branch takes
   its None arm (shadow 0 over the whole granule); rm_A_slow_ok: the out-of-line block 0x82610 itself has the shape
   the recognizer accepts. rm_A_80158_gran: for an input of 1 .. 7 bytes that obligation is false at data[0];
   rm_A_80158_cell: the shadow cell the route loads instead, and why its report arm is dead. *)
Definition rm_A_tbl80158 : ctable := build_table Img0.rsegs 0x80150 6 (build_table Img0.rsegs 0x82610 4 TEmpty).
Lemma rm_A_tbl80158_ok : table_ok Img0.rsegs rm_A_tbl80158.
Proof. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.

Lemma rm_A_tok_none : forall t, YCbn.slow_block rm_A_tbl80158 0x80160 0x80164 t = None.
Proof. intros t. vm_compute. reflexivity. Qed.
Lemma rm_A_tok_arm :
match YCbn.dec rm_A_tbl80158 0x80160 with
| Some i => match YCbn.as_andi i with Some _ => false | None => true end
| None => false end = true /\
YCbn.decp rm_A_tbl80158 YCbn.as_j 0x80160 = Some (0x82610 - 0x80160) /\
match YCbn.decp rm_A_tbl80158 YCbn.as_branch 0x8015c with
| Some (c, r1, r2, off) =>
  match c with BC_EQ => (bv_unsigned r1 =? 10) && (bv_unsigned r2 =? 0) && (off =? 8) | _ => false end
| None => false end = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rm_A_slow_ok :
match YCbn.slow_block rm_A_tbl80158 0x82610 0x80164 (Z_to_bv 5 10) with
| Some (u, xr, k) => (bv_unsigned u =? 11) && (bv_unsigned xr =? 12) && (k =? 0)
| None => false end = true.
Proof. vm_compute. reflexivity. Qed.

Section site. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Lemma rm_A_80158_gran : forall ly S W mem md p n,
AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n < 8 ->
~ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p 8.
Proof.
intros ly S W mem md p n HAR Hin Hn.
destruct (al_shadow _ _ (AR_laws_ok segs B) ly S W mem md p n HAR Hin) as [Hbs _].
unfold req_size in Hbs. replace (n =? 0) with false in Hbs by (symmetry; apply Z.eqb_neq; lia).
exact (rm_ra_gran_false _ _ p n Hbs Hn).
Qed.
Lemma rm_A_80158_cell : forall ly S W mem md p n,
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

Print Assumptions rm_bytes_patch.
Print Assumptions rm_bytes_field.
Print Assumptions rm_blk_ra.
Print Assumptions rm_ra_gran_false.
Print Assumptions rm_cell_region.
Print Assumptions rm_A_rz.
Print Assumptions rm_fsh_set.
Print Assumptions rm_A_ra_r.
Print Assumptions rm_fsh_of_chunks.
Print Assumptions rm_slots_chunk.
Print Assumptions rm_cut_kept.
Print Assumptions rm_keeps_call.
Print Assumptions rm_A_tok_none.
Print Assumptions rm_A_tok_arm.
Print Assumptions rm_A_slow_ok.
Print Assumptions rm_A_80158_gran.
Print Assumptions rm_A_80158_cell.
Print Assumptions rm_bytes_store.
Print Assumptions rm_pp_len.
Print Assumptions rm_pp_ent.
Print Assumptions rm_pp_buf.
Print Assumptions rm_ro_bytes.
Print Assumptions rm_ra_kept_wr.
Print Assumptions rm_rom_kept_wr.
Print Assumptions rm_ra_not_fsh.
Print Assumptions rm_shadow_not_app.
