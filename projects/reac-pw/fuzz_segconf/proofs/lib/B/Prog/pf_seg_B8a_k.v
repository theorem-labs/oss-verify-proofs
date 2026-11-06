(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_calls_equal on the ASan build of plugin-hostd/fuzz_command
   (0x89968, 135 instructions), in the shape of cgif_file_fuzzer's walks (lib/A/AChc.v, ACh1.v..ACh8.v): the
   symbolic executor over the position-abstract listing (CmdPaLib.v), the inline checks removed by the shadow tokens
   (PaShadow.v), and the strcmp wrapper's call stepped through by its contract (PaArt.v aj_art_at). The two loops
   are cut at their heads (0x899dc, 0x89a6c) and at the outer latch (0x89ab0); each piece is re-seeded from the
   concrete state there and the loops are proved by induction. Every call is strcmp, which writes only its stack
   window, so the memory below the frame stays the entry's (kept_out) and the read-only bytes strcmp reads
   (rt_rom_view) follow from the statement's arodata_okP. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_calls_equal.v, with its module paths, module names and numbers changed; 532 of its 679 lines of code are new or changed and 1344 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_segments_s1.v, with its module paths and module names changed; 177 of its 258 lines of code are new or changed and 598 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the pure kit of segment B8a of
   reac_segconf_parse_file's walk (lib/B/Prog/pf_pieces.v S_B8a: SEG 0x88ca0 -> NEW 0x88e54 / FOUND 0x88eb0 /
   REFTL 0x887cc, the inlined seg_get search of reac_segconf.c:103-118). The B8a segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: model and byte lemmas, no instruction walked).
   ADAPTED from the image-A G3 walk owner's image-A kit lib/A/Prog/pf_a8a_k.v (commit 61a728170142, part 1:
   the spine a8_ovf / a8_step_full / a8_find_step and the c->overflow + 1 encoding a8_rconf_ovf, which the image-A G3 walk owner
   copied from the unit owner's lib/Prog/pfB_p4_spine.v; the block's bytes a8_bytes_app .. a8_le4_byte, which it copied
   from the image-A G4/G5 walk owner's check_segments_s1.v); image-free, so the statements are A's with b8_ names; added for image B:
   the search invariant b8_find_inv / b8_find_hit / b8_find_miss in the loop's terms (B's loop carries the entry
   index i), the counters of the bound refusal at REFTL (b8_reftl_cnt: INV_REFTL's room after the line with one
   more refused, pf_pieces.v ba1c0e453663), and the store of c->overflow + 1 through a reader (b8_sa_rconf_ovf). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YP09 YI04 YP03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module PCS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_segments.CsPure.
Module PMem := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Mem.

(** ** 1. The spine *)
(* seg_get's bound branch (R:110): c->overflow + 1 *)
Definition b8_ovf (rc : rconf) : rconf :=
  RConf (rc_seg rc) (rc_refusal rc) (rc_refused rc) (rc_overflow rc + 1) (rc_reading rc) (rc_gen rc).
Lemma b8_step_full : forall cf nm ln name, r_find_go (rc_seg cf) name 0 = None -> (32 <= length (rc_seg cf))%nat ->
  pf_seg_step cf nm ln name = (refuse (b8_ovf cf) ln F_bound [AS name; AI 32], None, nm).
Proof.
intros cf nm ln name H1 H2. unfold pf_seg_step, seg_get. rewrite H1. apply Nat.leb_le in H2. rewrite H2. reflexivity.
Qed.
(* the search loop, one entry at a time *)
Lemma b8_find_step : forall segs name i k, (i < length segs)%nat ->
  r_find_go (skipn i segs) name k =
  if strcmp (rs_name (nth i segs rseg_d)) name =? 0 then Some k else r_find_go (skipn (S i) segs) name (S k).
Proof.
induction segs as [|g segs IH]; intros name i k H; cbn [length] in H; [lia|].
destruct i as [|i]; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.
Lemma b8_find_end : forall segs name k, r_find_go (skipn (length segs) segs) name k = None.
Proof. intros segs name k. rewrite skipn_all. reflexivity. Qed.
(* B's loop invariant: entries 0 .. i - 1 do not hold the name *)
Definition b8_find_inv (segs : list rseg) (name : list Z) (i : nat) : Prop :=
  r_find_go segs name 0 = r_find_go (skipn i segs) name i.
Lemma b8_find_inv0 : forall segs name, b8_find_inv segs name 0.
Proof. intros segs name. reflexivity. Qed.
Lemma b8_find_hit : forall segs name i, b8_find_inv segs name i -> (i < length segs)%nat ->
  strcmp (rs_name (nth i segs rseg_d)) name = 0 -> r_find_go segs name 0 = Some i.
Proof.
intros segs name i H Hi Hc. unfold b8_find_inv in H. rewrite H, (b8_find_step segs name i i Hi).
rewrite Hc. reflexivity.
Qed.
Lemma b8_find_next : forall segs name i, b8_find_inv segs name i -> (i < length segs)%nat ->
  strcmp (rs_name (nth i segs rseg_d)) name <> 0 -> b8_find_inv segs name (S i).
Proof.
intros segs name i H Hi Hc. unfold b8_find_inv in *. rewrite H, (b8_find_step segs name i i Hi).
apply Z.eqb_neq in Hc. rewrite Hc. reflexivity.
Qed.
Lemma b8_find_miss : forall segs name, b8_find_inv segs name (length segs) -> r_find_go segs name 0 = None.
Proof. intros segs name H. unfold b8_find_inv in H. rewrite H. apply b8_find_end. Qed.

(** ** 2. The counters of the bound refusal (INV_REFTL, pf_pieces.v ba1c0e453663) *)
Lemma b8_reftl_cnt : forall s o cf, (o < length s)%nat -> pf_cnt cf (length (skipn o s)) ->
  pf_cnt (b8_ovf cf) (length (skipn (pf_next s o) s)) /\
  rc_refused (b8_ovf cf) + Z.of_nat (length (skipn (pf_next s o) s)) + 1 + 2 ^ 16 < 2 ^ 32 /\
  rc_overflow cf + 1 < 2 ^ 32.
Proof.
intros s o cf Ho [H1 H2]. pose proof (pf_next_skipn_lt s o Ho) as L.
unfold pf_cnt, b8_ovf. cbn [rc_refused rc_overflow]. split; [split|]; lia.
Qed.

(** ** 3. c->overflow + 1 in the encoding *)
Lemma b8_nth_error_fld : forall (l : list byte) a n i,
  nth_error (seg_spec.fld a n l) i = if (i <? n)%nat then nth_error l (a + i) else None.
Proof.
intros l a n i. unfold seg_spec.fld. rewrite nth_error_firstn. destruct (i <? n)%nat; [|reflexivity].
rewrite nth_error_skipn. f_equal; lia.
Qed.
Lemma b8_upd_nth_error : forall (l ws : list byte) k i, (k + length ws <= length l)%nat ->
  nth_error (PMem.upd_bytes l k ws) i =
    if (k <=? i)%nat && (i <? k + length ws)%nat then nth_error ws (i - k) else nth_error l i.
Proof.
intros l ws k i H. destruct (Nat.lt_ge_cases i (length l)) as [Hi|Hi].
- apply PMem.upd_bytes_nth; assumption.
- rewrite (proj2 (nth_error_None (PMem.upd_bytes l k ws) i)) by (rewrite PMem.upd_bytes_length; lia).
  rewrite (proj2 (nth_error_None l i)) by lia.
  destruct (Nat.leb_spec0 k i), (Nat.ltb_spec0 i (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma b8_nth_of_err : forall {A} (l l' : list A) i j d, nth_error l i = nth_error l' j -> nth i l d = nth j l' d.
Proof. intros A l l' i j d H. rewrite <- !nth_default_eq. unfold nth_default. rewrite H. reflexivity. Qed.
Lemma b8_fld_upd_out : forall (l ws : list byte) k a n, (k + length ws <= length l)%nat ->
  (a + n <= k \/ k + length ws <= a)%nat -> seg_spec.fld a n (PMem.upd_bytes l k ws) = seg_spec.fld a n l.
Proof.
intros l ws k a n H D. apply nth_error_ext. intros i. rewrite !b8_nth_error_fld.
destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite b8_upd_nth_error by exact H.
destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length ws)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma b8_fld_upd_same : forall (l ws : list byte) k n, (k + length ws <= length l)%nat -> length ws = n ->
  seg_spec.fld k n (PMem.upd_bytes l k ws) = ws.
Proof.
intros l ws k n H <-. apply nth_error_ext. intros i. rewrite b8_nth_error_fld.
destruct (Nat.ltb_spec0 i (length ws)).
- rewrite b8_upd_nth_error by exact H.
  destruct (Nat.leb_spec0 k (k + i)), (Nat.ltb_spec0 (k + i) (k + length ws)); cbn [andb]; try lia.
  f_equal. lia.
- symmetry. apply nth_error_None. lia.
Qed.
Lemma b8_rconf_ovf : forall rc bs, seg_spec.rconf_enc rc bs -> rc_overflow rc + 1 < 2 ^ 32 ->
  seg_spec.rconf_enc (b8_ovf rc)
    (PMem.upd_bytes bs (Z.to_nat seg_spec.RC_OVERFLOW) (PMem.le4 (Z_to_bv 64 (rc_overflow rc + 1)))).
Proof.
intros rc bs (L & LS & SEGS & N & LR & REF & NR & RF & OV & RD & GEN) Hov.
unfold seg_spec.SEG_C_SIZE in L. unfold b8_ovf, seg_spec.rconf_enc.
cbn [rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen].
unfold seg_spec.fldz, seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_NREF, seg_spec.RC_REFUSED,
  seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN in *.
assert (Lw : length (PMem.le4 (Z_to_bv 64 (rc_overflow rc + 1))) = 4%nat) by apply PMem.length_le4.
pose proof OV as ((OV0 & _) & _).
assert (O : forall a n, (a + n <= Z.to_nat 13520 \/ Z.to_nat 13524 <= a)%nat ->
          seg_spec.fld a n (PMem.upd_bytes bs (Z.to_nat 13520) (PMem.le4 (Z_to_bv 64 (rc_overflow rc + 1)))) =
          seg_spec.fld a n bs).
{ intros a n D. apply b8_fld_upd_out; lia. }
split; [unfold seg_spec.SEG_C_SIZE; rewrite PMem.upd_bytes_length; lia|].
split; [exact LS|].
split; [intros j Hj; rewrite O by lia; apply SEGS; exact Hj|].
split; [rewrite O by lia; exact N|].
split; [exact LR|].
split; [intros j Hj; rewrite O by lia; apply REF; exact Hj|].
split; [rewrite O by lia; exact NR|].
split; [rewrite O by lia; exact RF|].
split; [rewrite b8_fld_upd_same by lia; split; [lia | reflexivity]|].
split; [rewrite O by lia; exact RD|].
rewrite O by lia; exact GEN.
Qed.

(** ** 4. Bytes of the block through a reader *)
Lemma b8_bytes_app : forall (rd : reader) a l1 l2, sa_bytes rd a (l1 ++ l2) ->
  sa_bytes rd a l1 /\ sa_bytes rd (a + Z.of_nat (length l1)) l2.
Proof.
intros rd a l1 l2 H. split.
- intros i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity.
- intros i Hi. replace (a + Z.of_nat (length l1) + Z.of_nat i) with (a + Z.of_nat (length l1 + i)) by lia.
  rewrite (H (length l1 + i)%nat) by (rewrite length_app; lia). rewrite app_nth2 by lia.
  replace (length l1 + i - length l1)%nat with i by lia. reflexivity.
Qed.
Lemma b8_bytes_sub : forall (rd : reader) a bs k l, sa_bytes rd a bs -> (k + l <= length bs)%nat ->
  sa_bytes rd (a + Z.of_nat k) (firstn l (skipn k bs)).
Proof.
intros rd a bs k l H Hl.
rewrite <- (firstn_skipn k bs) in H. apply b8_bytes_app in H as [_ H].
rewrite length_firstn, Nat.min_l in H by lia.
rewrite <- (firstn_skipn l (skipn k bs)) in H. apply b8_bytes_app in H as [H _]. exact H.
Qed.
Lemma b8_cstr : forall (rd : reader) a f cap s, sa_bytes rd a f -> (cap <= length f)%nat ->
  seg_spec.cstr_enc cap s (firstn cap f) ->
  exists sx, sa_bytes rd a (sx ++ [seg_spec.ZERO]) /\ ~ In seg_spec.ZERO sx /\ seg_spec.zs sx = s /\ (length sx < cap)%nat.
Proof.
intros rd a f cap s H Hc (_ & Ls & N & E).
rewrite PCS.firstn_zs, firstn_firstn, Nat.min_l in E by lia.
remember (firstn (S (length s)) f) as g eqn:Hg.
assert (Lg : length g = S (length s)) by (subst g; rewrite length_firstn; lia).
destruct (skipn (length s) g) as [|b [|b' r]] eqn:Sk.
- apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
- assert (Eg : g = firstn (length s) g ++ [b]) by (rewrite <- Sk; symmetry; apply firstn_skipn).
  rewrite Eg in E. unfold seg_spec.zs in E. rewrite map_app in E. cbn [map] in E.
  apply app_inj_tail in E as [E1 E2].
  assert (Eb : b = seg_spec.ZERO) by (apply bv_eq; rewrite E2; reflexivity). subst b.
  exists (firstn (length s) g). split; [|split; [|split]].
  + rewrite <- Eg, Hg. rewrite <- (firstn_skipn (S (length s)) f) in H.
    apply b8_bytes_app in H as [H _]. exact H.
  + apply PCS.zs_nul. unfold seg_spec.zs. rewrite E1. exact N.
  + unfold seg_spec.zs. exact E1.
  + rewrite length_firstn. lia.
- apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
Qed.
(* the name of c->seg[i] (offset 0 of its 356-byte entry) as strcmp's contract states a string *)
Lemma b8_rname : forall (rd : reader) c rcs i, sa_rconf rd c rcs -> (i < length (rc_seg rcs))%nat ->
  exists sx, sa_bytes rd (c + 356 * Z.of_nat i) (sx ++ [seg_spec.ZERO]) /\ ~ In seg_spec.ZERO sx /\
             seg_spec.zs sx = rs_name (nth i (rc_seg rcs) rseg_d) /\ (length sx < 16)%nat.
Proof.
intros rd c rcs i (bs & H & L & L32 & HS & _) Hi.
destruct (HS i Hi) as (Lf & Hn & _).
unfold seg_spec.SEG_C_SIZE in L.
assert (B : sa_bytes rd (c + Z.of_nat (356 * i)) (seg_spec.fld (356 * i) 356 bs))
  by (unfold seg_spec.fld; apply b8_bytes_sub; [exact H | lia]).
replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
apply (b8_cstr rd _ _ 16 _ B); [lia | exact Hn].
Qed.
Lemma b8_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (PMem.le4 (Z_to_bv 64 v)) seg_spec.ZERO) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold PMem.le4. rewrite unsigned_lit_small by lia.
unfold le_byte. change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth Z.of_nat];
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256;
rewrite ?Z.shiftr_shiftr by lia; rewrite ?Z.mul_0_r, ?Z.shiftr_0_r; try reflexivity; f_equal; f_equal; lia.
Qed.
(* the u32 field at k of a struct read through a reader *)
Lemma b8_u32_at : forall (rd : reader) a bs k v, sa_bytes rd a bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  seg_spec.u32_enc v (seg_spec.fldz k 4 bs) -> sa_val rd (a + k) 4 v.
Proof.
intros rd a bs k v H Hk Hl (Hv & E) j Hj.
replace (a + k + Z.of_nat j) with (a + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (H (Z.to_nat k + j)%nat) by lia. f_equal.
rewrite <- (b8_le4_byte v j Hv Hj). rewrite <- E. unfold seg_spec.fldz, seg_spec.fld.
change (Z.to_nat 4) with 4%nat. rewrite nth_firstn, nth_skipn.
replace (j <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). reflexivity.
Qed.
(* c->n and c->overflow through a reader that holds c *)
Lemma b8_rconf_n : forall (rd : reader) c rcs, sa_rconf rd c rcs ->
  sa_val rd (c + seg_spec.RC_N) 4 (Z.of_nat (length (rc_seg rcs))) /\ (length (rc_seg rcs) <= 32)%nat.
Proof.
intros rd c rcs (bs & H & L & L32 & _ & UN & _). unfold seg_spec.SEG_C_SIZE in L.
split; [|exact L32]. apply (b8_u32_at rd c bs); [exact H | unfold seg_spec.RC_N; lia | unfold seg_spec.RC_N; lia | exact UN].
Qed.
Lemma b8_rconf_ov : forall (rd : reader) c rcs, sa_rconf rd c rcs ->
  sa_val rd (c + seg_spec.RC_OVERFLOW) 4 (rc_overflow rcs) /\ 0 <= rc_overflow rcs < 2 ^ 32.
Proof.
intros rd c rcs (bs & H & L & _ & _ & _ & _ & _ & _ & _ & UO & _). unfold seg_spec.SEG_C_SIZE in L.
split; [|exact (proj1 UO)].
apply (b8_u32_at rd c bs); [exact H | unfold seg_spec.RC_OVERFLOW; lia | unfold seg_spec.RC_OVERFLOW; lia | exact UO].
Qed.
(* every byte of the block is mapped *)
Lemma b8_rconf_some : forall (rd : reader) c rcs a, sa_rconf rd c rcs -> c <= a < c + seg_spec.SEG_C_SIZE ->
  rd a <> None.
Proof.
intros rd c rcs a (bs & H & L & _) Ha. unfold seg_spec.SEG_C_SIZE in *.
replace a with (c + Z.of_nat (Z.to_nat (a - c))) by lia. rewrite H by lia. discriminate.
Qed.

(** ** 5. c->overflow + 1 stored through a reader *)
(* the reader rd' agrees with rd on the block off the four bytes of c->overflow, which hold v + 1 *)
Lemma b8_sa_rconf_ovf : forall (rd rd' : reader) c rcs, sa_rconf rd c rcs -> rc_overflow rcs + 1 < 2 ^ 32 ->
  (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> ~ (c + seg_spec.RC_OVERFLOW <= a < c + seg_spec.RC_OVERFLOW + 4) ->
   rd' a = rd a) ->
  sa_val rd' (c + seg_spec.RC_OVERFLOW) 4 (rc_overflow rcs + 1) ->
  sa_rconf rd' c (b8_ovf rcs).
Proof.
intros rd rd' c rcs (bs & HB & HE) Hov HK HV.
pose proof HE as (L & _ & _ & _ & _ & _ & _ & _ & ((OV0 & _) & _) & _).
unfold seg_spec.SEG_C_SIZE in L.
exists (PMem.upd_bytes bs (Z.to_nat seg_spec.RC_OVERFLOW) (PMem.le4 (Z_to_bv 64 (rc_overflow rcs + 1)))).
split; [|exact (b8_rconf_ovf rcs bs HE Hov)].
assert (Lw : length (PMem.le4 (Z_to_bv 64 (rc_overflow rcs + 1))) = 4%nat) by apply PMem.length_le4.
unfold seg_spec.RC_OVERFLOW in *.
intros i Hi. rewrite PMem.upd_bytes_length in Hi by lia.
pose proof (b8_upd_nth_error bs (PMem.le4 (Z_to_bv 64 (rc_overflow rcs + 1))) (Z.to_nat 13520) i ltac:(lia)) as U.
rewrite Lw in U.
destruct (Z_lt_le_dec (Z.of_nat i) 13520) as [Hlt|Hge]; [|destruct (Z_lt_le_dec (Z.of_nat i) 13524) as [Hin|Hout]].
- replace ((Z.to_nat 13520 <=? i)%nat) with false in U by (symmetry; apply Nat.leb_gt; lia). cbn [andb] in U.
  rewrite HK by (unfold seg_spec.SEG_C_SIZE; lia). rewrite (HB i Hi). f_equal. f_equal. apply b8_nth_of_err. symmetry. exact U.
- (* one of the four bytes of c->overflow *)
  replace ((Z.to_nat 13520 <=? i)%nat) with true in U by (symmetry; apply Nat.leb_le; lia).
  replace ((i <? Z.to_nat 13520 + 4)%nat) with true in U by (symmetry; apply Nat.ltb_lt; lia). cbn [andb] in U.
  replace (c + Z.of_nat i) with (c + 13520 + Z.of_nat (i - Z.to_nat 13520)) by lia.
  rewrite (HV (i - Z.to_nat 13520)%nat) by lia.
  rewrite <- (b8_le4_byte (rc_overflow rcs + 1) (i - Z.to_nat 13520) ltac:(lia) ltac:(lia)).
  f_equal. f_equal. rewrite (b8_nth_of_err _ _ i _ ZB0 U).
  apply nth_indep. rewrite Lw. lia.
- replace ((i <? Z.to_nat 13520 + 4)%nat) with false in U by (symmetry; apply Nat.ltb_ge; lia).
  rewrite andb_false_r in U.
  rewrite HK by (unfold seg_spec.SEG_C_SIZE; lia). rewrite (HB i Hi). f_equal. f_equal. apply b8_nth_of_err. symmetry. exact U.
Qed.

(** ** 6. strcmp's answer on the i-th name *)
(* the strings strcmp's contract states are byte lists; the model's names are lists of Z *)
Lemma b8_strcmp_eq : forall (sx : list byte) (name : list Z), ~ In seg_spec.ZERO sx -> ~ In 0 name ->
  Forall (fun x => 0 <= x < 256) name ->
  (sx = seg_spec.zb name <-> strcmp (seg_spec.zs sx) name = 0).
Proof.
intros sx name Nx Nn Rn.
assert (Zn : seg_spec.zs (seg_spec.zb name) = name).
{ unfold seg_spec.zs, seg_spec.zb. clear Nn. induction name as [|x name IH]; [reflexivity|].
  inversion Rn as [|? ? Hx Hl]; subst. cbn [map]. f_equal; [|exact (IH Hl)].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. }
assert (Nb : ~ In seg_spec.ZERO (seg_spec.zb name)) by (apply PCS.zs_nul; rewrite Zn; exact Nn).
rewrite <- Zn at 2. symmetry. exact (PCS.bridge_strcmp sx (seg_spec.zb name) Nx Nb).
Qed.
