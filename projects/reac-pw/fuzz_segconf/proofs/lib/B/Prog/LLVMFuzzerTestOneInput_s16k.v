(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the call of send_message in LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, jal at 0x86714, back at 0x86718), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v:122-290 (a program call through cl_callS, the callee's statement applied, the caller's facts carried past it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s30.v, with its module paths and module names changed; 622 of its 671 lines of code are new or changed and 292 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s20k.v, with its module paths and module names changed; 789 of its 861 lines of code are new or changed and 599 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s16k.v, with its module paths and module names changed; 277 of its 392 lines of code are new or changed and 746 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of segment S06
   of the walk of the test harness's entry function LLVMFuzzerTestOneInput, the inlined m_cross loop
   (0x85338 .. 0x854d0, fuzz_segconf.c:296-310) with its two m_refuse calls (0x853f0, 0x85424). Model and encoding
   facts only: no instruction of the binary is stepped here; LLVMFuzzerTestOneInput_s16.v walks the code.
   - The model: after i turns the loop holds fold_left m_cross_seg (seq 0 i) M0 (s6_step), whose table keeps its
     length (s6_len) and whose refused counter grows by at most one a turn (s6_cnt); one turn is nothing, or a
     refusal with one of the two edits of entry i (s6_seg_cases); the counters before the last turn are below its bound
     (s6_run_refused, from m_file_c.m_file_refused and SegModel.decode_ok), so lt_cnt holds after m_cross.
   - The struct mconf through the reader (SegABase.sa_mconf): the words the loop loads (m->n, and role, role_set,
     model_set of m->seg[i]) as rd32 facts, and the struct after the loop's stores of zero: model_set = 0 (c:303)
     holds m_upd mc i ms_drop_model, role = 0 and role_set = 0 (c:306-307) hold m_upd mc i ms_drop_role.
   The byte-list lemmas (s6_fld_*, s6_mseg_drop_*, s6_mconf_upd) are the image-B owner's plain lib/Prog/Seg/L02W_mx.v
   (the plain walk, mx_* there) restated over the ASan reader; the image-A twin (image A's S06 walk) had
   pushed no file when this was written. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YP03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require m_file_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

(* ===================================== the model ===================================== *)
(* m_cross's input on the last turn f, and the table after its first i passes *)
Definition s6_M0 (pl : list byte) (f : nat) : mconf :=
  m_file (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f) None.
Definition s6_MI (pl : list byte) (f i : nat) : mconf := fold_left m_cross_seg (seq 0 i) (s6_M0 pl f).

Lemma s6_upd_nth_length : forall {A} i (g : A -> A) l, length (upd_nth i g l) = length l.
Proof. intros A i g l. revert i. induction l as [|x l IH]; intros [|i]; cbn [upd_nth length]; auto. Qed.
Lemma s6_upd_nth_nth : forall {A} i j (g : A -> A) l d, (i < length l)%nat ->
  nth j (upd_nth i g l) d = if Nat.eqb j i then g (nth i l d) else nth j l d.
Proof.
intros A i j g l d. revert i j. induction l as [|x l IH]; intros i j Hi; cbn [length] in Hi; [lia|].
destruct i as [|i], j as [|j]; cbn [upd_nth nth Nat.eqb]; try reflexivity. apply IH. lia.
Qed.

(* one pass, by the entry's three fields *)
Lemma s6_seg_eq : forall c i,
  m_cross_seg c i =
  (let g := nth i (mc_seg c) mseg_d in
   let box := ms_role_set g && (ms_role g =? 4) in
   if ms_model_set g && negb box then m_upd (m_refuse c 0 false) i ms_drop_model
   else if box && negb (ms_model_set g) then m_upd (m_refuse c 0 false) i ms_drop_role
   else c).
Proof. reflexivity. Qed.
Lemma s6_seg_cases : forall c i,
  m_cross_seg c i = m_upd (m_refuse c 0 false) i ms_drop_model \/
  m_cross_seg c i = m_upd (m_refuse c 0 false) i ms_drop_role \/ m_cross_seg c i = c.
Proof.
intros c i. unfold m_cross_seg. cbv zeta.
match goal with |- context [if ?b then _ else _] => destruct b end; [left; reflexivity|].
match goal with |- context [if ?b then _ else _] => destruct b end; [right; left; reflexivity|].
right; right; reflexivity.
Qed.
Lemma s6_seg_len : forall c i, length (mc_seg (m_cross_seg c i)) = length (mc_seg c).
Proof.
intros c i. destruct (s6_seg_cases c i) as [E|[E|E]]; rewrite E; try reflexivity;
  unfold m_upd, m_set_segs; cbn [mc_seg m_refuse]; apply s6_upd_nth_length.
Qed.
Lemma s6_seg_cnt : forall c i,
  mc_gen (m_cross_seg c i) = mc_gen c /\ mc_overflow (m_cross_seg c i) = mc_overflow c /\
  mc_refused c <= mc_refused (m_cross_seg c i) <= mc_refused c + 1.
Proof. intros c i. destruct (s6_seg_cases c i) as [E|[E|E]]; rewrite E; cbn; lia. Qed.
Lemma s6_step : forall m1 i,
  fold_left m_cross_seg (seq 0 (S i)) m1 = m_cross_seg (fold_left m_cross_seg (seq 0 i) m1) i.
Proof. intros m1 i. rewrite seq_S, fold_left_app. reflexivity. Qed.
Lemma s6_len : forall m1 i, length (mc_seg (fold_left m_cross_seg (seq 0 i) m1)) = length (mc_seg m1).
Proof. intros m1 i. induction i as [|i IH]; [reflexivity|]. rewrite s6_step, s6_seg_len. exact IH. Qed.
Lemma s6_cnt : forall m1 i,
  mc_gen (fold_left m_cross_seg (seq 0 i) m1) = mc_gen m1 /\
  mc_overflow (fold_left m_cross_seg (seq 0 i) m1) = mc_overflow m1 /\
  mc_refused m1 <= mc_refused (fold_left m_cross_seg (seq 0 i) m1) <= mc_refused m1 + Z.of_nat i.
Proof.
intros m1 i. induction i as [|i IH]; [cbn; lia|].
rewrite s6_step. pose proof (s6_seg_cnt (fold_left m_cross_seg (seq 0 i) m1) i). lia.
Qed.
Lemma s6_all : forall m1, m_cross m1 = fold_left m_cross_seg (seq 0 (length (mc_seg m1))) m1.
Proof. reflexivity. Qed.

(* every text the payload decodes to is NUL-free and at most 65535 bytes long *)
Lemma s6_txt_ok : forall pl k,
  nulfree (seg_spec.seg_txt pl k) /\ Z.of_nat (length (seg_spec.seg_txt pl k)) <= 65535.
Proof.
intros pl k. unfold seg_spec.seg_txt, seg_spec.seg_file.
assert (HF : Forall file_ok (seg_spec.seg_files pl)).
{ unfold seg_spec.seg_files, seg_spec.seg_pay. apply decode_ok.
  unfold seg_spec.seg_in, seg_spec.zs. apply Forall_forall. intros x Hx.
  apply in_map_iff in Hx as (b & <- & _). unfold byte_ok.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
destruct (Nat.lt_ge_cases k (length (seg_spec.seg_files pl))) as [Hk|Hk].
- rewrite Forall_forall in HF. destruct (HF _ (nth_In _ (File 0 []) Hk)) as (H1 & H2 & _). split; assumption.
- rewrite nth_overflow by exact Hk. cbn [f_text length]. split; [intros [] | lia].
Qed.
(* the refusals counted before turn f: each drop-in turn's m_file refuses at most once a line *)
Lemma s6_run_refused : forall pl f,
  0 <= mc_refused (seg_spec.seg_mc (seg_spec.seg_run pl f)) <= Z.of_nat f * 65535.
Proof.
intros pl f. induction f as [|f IH]; [cbn; lia|].
cbn [seg_spec.seg_run]. unfold seg_spec.seg_turn_step.
destruct (seg_spec.seg_run pl f) as [[c mc] ret] eqn:Est. cbv beta iota.
destruct (r_parse_file c (seg_spec.seg_txt pl f) (seg_spec.seg_label pl f)) as [c1 n].
unfold seg_spec.seg_mc in IH |- *. cbn [fst snd] in IH |- *.
destruct (s6_txt_ok pl f) as [Hn Hl].
pose proof (m_file_c.m_file_refused mc (seg_spec.seg_txt pl f) (seg_spec.seg_label pl f) Hn) as H. lia.
Qed.
Lemma s6_M0_refused : forall pl f,
  0 <= mc_refused (s6_M0 pl f) <= Z.of_nat (S f) * 65535.
Proof.
intros pl f. unfold s6_M0. pose proof (s6_run_refused pl f) as H0.
destruct (s6_txt_ok pl f) as [Hn Hl].
pose proof (m_file_c.m_file_refused (seg_spec.seg_mc (seg_spec.seg_run pl f)) (seg_spec.seg_txt pl f) None Hn) as H.
lia.
Qed.

(* ===================================== byte lists ===================================== *)
Lemma s6_nth_firstn : forall {A} (l : list A) h i d, (i < h)%nat -> nth i (firstn h l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros h i d Hi; [destruct h; reflexivity|].
destruct h as [|h]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s6_nth_skipn : forall {A} (l : list A) s i d, nth i (skipn s l) d = nth (s + i) l d.
Proof.
intros A l s. revert l. induction s as [|s IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.
Lemma s6_nth_fld : forall (l : list byte) a n i d, (i < n)%nat -> nth i (seg_spec.fld a n l) d = nth (a + i) l d.
Proof. intros l a n i d Hi. unfold seg_spec.fld. rewrite s6_nth_firstn by exact Hi. apply s6_nth_skipn. Qed.
Lemma s6_nth_error_fld : forall (l : list byte) a n i,
  nth_error (seg_spec.fld a n l) i = if Nat.ltb i n then nth_error l (a + i) else None.
Proof.
intros l a n i. unfold seg_spec.fld. rewrite nth_error_firstn, nth_error_skipn.
destruct (Nat.ltb_spec0 i n); reflexivity.
Qed.
(* a byte of the 4 little-endian bytes of v *)
Lemma s6_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) seg_spec.ZERO) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4. rewrite unsigned_lit_small by lia. unfold le_byte.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia).
assert (E : forall z, bv_unsigned (Z_to_bv 8 z) = z mod 256)
  by (intros z; rewrite Z_to_bv_unsigned; reflexivity).
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth]; rewrite E;
  rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
(* a 4-byte field of a block read through the reader *)
Lemma s6_rd32_of : forall (rd : reader) a bs o v, sa_bytes rd a bs -> (o + 4 <= length bs)%nat ->
  seg_spec.fld o 4 bs = Mem.le4 (Z_to_bv 64 v) -> 0 <= v < 2 ^ 32 -> rd32 rd (a + Z.of_nat o) v.
Proof.
intros rd a bs o v HB Hl Hf Hv k Hk.
replace (a + Z.of_nat o + Z.of_nat k) with (a + Z.of_nat (o + k)) by lia.
rewrite (HB (o + k)%nat ltac:(lia)). f_equal.
rewrite <- (s6_nth_fld bs o 4 k ZB0 Hk). rewrite Hf. exact (s6_le4_byte v k Hv Hk).
Qed.

(* the encoding of one entry and of the struct after one entry is edited in place *)
Definition s6_Z4 : list byte := Mem.le4 (Z_to_bv 64 0).
Lemma s6_Z4_len : length s6_Z4 = 4%nat.
Proof. apply Mem.length_le4. Qed.
Lemma s6_nth_upd : forall (bs X : list byte) k j, (k + length X <= length bs)%nat ->
  nth_error (Mem.upd_bytes bs k X) j =
    if (Nat.leb k j && Nat.ltb j (k + length X))%bool then nth_error X (j - k) else nth_error bs j.
Proof.
intros bs X k j H. destruct (Nat.ltb_spec0 j (length bs)) as [L|L].
- apply Mem.upd_bytes_nth; assumption.
- rewrite (proj2 (nth_error_None (Mem.upd_bytes bs k X) j)) by (rewrite Mem.upd_bytes_length by assumption; lia).
  rewrite (proj2 (nth_error_None bs j)) by lia.
  destruct (Nat.leb_spec0 k j), (Nat.ltb_spec0 j (k + length X)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma s6_fld_upd_out : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (a + n <= k \/ k + length X <= a)%nat ->
  seg_spec.fld a n (Mem.upd_bytes bs k X) = seg_spec.fld a n bs.
Proof.
intros bs X k a n H D. apply nth_error_ext. intros i. rewrite !s6_nth_error_fld.
destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite (s6_nth_upd bs X k (a + i) H).
destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb]; try reflexivity. lia.
Qed.
Lemma s6_fld_upd_inner : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (k <= a)%nat -> (a + n <= k + length X)%nat ->
  seg_spec.fld a n (Mem.upd_bytes bs k X) = seg_spec.fld (a - k) n X.
Proof.
intros bs X k a n H1 H2 H3. apply nth_error_ext. intros i. rewrite !s6_nth_error_fld.
destruct (Nat.ltb_spec0 i n); [|reflexivity]. rewrite (s6_nth_upd bs X k (a + i) H1).
destruct (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb]; try lia.
f_equal. lia.
Qed.
Lemma s6_fld_upd_sub : forall (bs X : list byte) k a n,
  (k + length X <= length bs)%nat -> (a <= k)%nat -> (k + length X <= a + n)%nat -> (a + n <= length bs)%nat ->
  seg_spec.fld a n (Mem.upd_bytes bs k X) = Mem.upd_bytes (seg_spec.fld a n bs) (k - a) X.
Proof.
intros bs X k a n H1 H2 H3 H4.
assert (LF : length (seg_spec.fld a n bs) = n)
  by (unfold seg_spec.fld; rewrite length_firstn, length_skipn; lia).
apply nth_error_ext. intros i.
rewrite (s6_nth_upd (seg_spec.fld a n bs) X (k - a) i) by lia.
rewrite !s6_nth_error_fld. rewrite (s6_nth_upd bs X k (a + i) H1).
destruct (Nat.ltb_spec0 i n), (Nat.leb_spec0 (k - a) i), (Nat.ltb_spec0 i (k - a + length X)),
         (Nat.leb_spec0 k (a + i)), (Nat.ltb_spec0 (a + i) (k + length X)); cbn [andb];
  try (exfalso; lia); try reflexivity.
f_equal. lia.
Qed.
Lemma s6_mseg_drop_model : forall g f, seg_spec.mseg_enc g f ->
  seg_spec.mseg_enc (ms_drop_model g) (Mem.upd_bytes f 32 s6_Z4).
Proof.
intros g f (L & N & R & RS & I & IS & MS & M & RF & IF & G).
assert (HL : (32 + length s6_Z4 <= length f)%nat) by (rewrite s6_Z4_len; lia).
unfold ms_drop_model, seg_spec.mseg_enc. cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set
  ms_model ms_role_file ms_ignore_file ms_gen].
unfold seg_spec.fldz in *. unfold seg_spec.MS_ROLE, seg_spec.MS_ROLE_SET, seg_spec.MS_IGNORE, seg_spec.MS_IGNORE_SET,
  seg_spec.MS_MODEL_SET, seg_spec.MS_MODEL, seg_spec.MS_ROLE_FILE, seg_spec.MS_IGNORE_FILE, seg_spec.MS_GEN in *.
split; [rewrite Mem.upd_bytes_length by exact HL; exact L|].
rewrite (s6_fld_upd_inner f s6_Z4 32 (Z.to_nat 32) (Z.to_nat 4)) by (rewrite ?s6_Z4_len; lia).
rewrite !(s6_fld_upd_out f s6_Z4 32) by (rewrite ?s6_Z4_len; lia).
refine (conj N (conj R (conj RS (conj I (conj IS (conj _ (conj M (conj RF (conj IF G))))))))).
reflexivity.
Qed.
Lemma s6_mseg_drop_role : forall g f, seg_spec.mseg_enc g f ->
  seg_spec.mseg_enc (ms_drop_role g) (Mem.upd_bytes f 16 (s6_Z4 ++ s6_Z4)).
Proof.
intros g f (L & N & R & RS & I & IS & MS & M & RF & IF & G).
assert (HL : (16 + length (s6_Z4 ++ s6_Z4) <= length f)%nat) by (rewrite length_app, s6_Z4_len; lia).
unfold ms_drop_role, seg_spec.mseg_enc. cbn [ms_name ms_role ms_role_set ms_ignore ms_ignore_set ms_model_set
  ms_model ms_role_file ms_ignore_file ms_gen].
unfold seg_spec.fldz in *. unfold seg_spec.MS_ROLE, seg_spec.MS_ROLE_SET, seg_spec.MS_IGNORE, seg_spec.MS_IGNORE_SET,
  seg_spec.MS_MODEL_SET, seg_spec.MS_MODEL, seg_spec.MS_ROLE_FILE, seg_spec.MS_IGNORE_FILE, seg_spec.MS_GEN in *.
split; [rewrite Mem.upd_bytes_length by exact HL; exact L|].
rewrite (s6_fld_upd_inner f (s6_Z4 ++ s6_Z4) 16 (Z.to_nat 16) (Z.to_nat 4)) by (rewrite ?length_app, ?s6_Z4_len; lia).
rewrite (s6_fld_upd_inner f (s6_Z4 ++ s6_Z4) 16 (Z.to_nat 20) (Z.to_nat 4)) by (rewrite ?length_app, ?s6_Z4_len; lia).
rewrite !(s6_fld_upd_out f (s6_Z4 ++ s6_Z4) 16) by (rewrite ?length_app, ?s6_Z4_len; lia).
refine (conj N (conj _ (conj _ (conj I (conj IS (conj MS (conj M (conj RF (conj IF G))))))))).
- split; [split; [lia | reflexivity] | lia].
- reflexivity.
Qed.
Lemma s6_mconf_upd : forall mc bs i g X off,
  seg_spec.mconf_enc mc bs -> (i < length (mc_seg mc))%nat -> (off + length X <= 256)%nat ->
  seg_spec.mseg_enc (g (nth i (mc_seg mc) mseg_d)) (Mem.upd_bytes (seg_spec.fld (256 * i) 256 bs) off X) ->
  seg_spec.mconf_enc (m_upd mc i g) (Mem.upd_bytes bs (256 * i + off) X).
Proof.
intros mc bs i g X off E Hi HX HG.
destruct E as (L & LS & SG & N & O & RF & LK & KP & KN & NK & G & RD).
unfold seg_spec.SEG_M_SIZE in L.
assert (HB : (256 * i + off + length X <= length bs)%nat) by lia.
assert (OUT : forall a n, (256 * 32 <= a)%nat -> seg_spec.fld a n (Mem.upd_bytes bs (256 * i + off) X) = seg_spec.fld a n bs)
  by (intros a n Ha; apply s6_fld_upd_out; [exact HB | right; lia]).
unfold seg_spec.mconf_enc, seg_spec.mconf_encp, seg_spec.fldz in *. unfold m_upd, m_set_segs.
cbn [mc_seg mc_overflow mc_refused mc_kept mc_gen mc_reading].
unfold seg_spec.MC_N, seg_spec.MC_OVERFLOW, seg_spec.MC_REFUSED, seg_spec.MC_KEPT, seg_spec.MC_KNOCK,
  seg_spec.MC_NKEPT, seg_spec.MC_GEN, seg_spec.MC_READING in *.
rewrite !s6_upd_nth_length.
split; [rewrite Mem.upd_bytes_length by exact HB; unfold seg_spec.SEG_M_SIZE; exact L|]. split; [exact LS|].
split.
{ intros j Hj. rewrite (s6_upd_nth_nth i j g (mc_seg mc) mseg_d Hi).
  destruct (Nat.eqb_spec j i) as [->|Ne].
  - rewrite (s6_fld_upd_sub bs X (256 * i + off) (256 * i) 256) by lia.
    replace (256 * i + off - 256 * i)%nat with off by lia. exact HG.
  - rewrite (s6_fld_upd_out bs X (256 * i + off) (256 * j) 256) by lia. apply SG. exact Hj. }
rewrite !OUT by lia.
split; [exact N|]. split; [exact O|]. split; [exact RF|]. split; [exact LK|].
split; [intros j Hj; rewrite !OUT by lia; apply KP; exact Hj|].
split; [intros j Hj; rewrite !OUT by lia; apply KN; exact Hj|].
split; [exact NK|]. split; [exact G|exact RD].
Qed.

(* ===================================== the struct through a reader ===================================== *)
Section r.
Variable rd : reader.

Lemma s6_mconf_len : forall m mc, sa_mconf rd m mc -> (length (mc_seg mc) <= 32)%nat.
Proof. intros m mc (bs & _ & _ & LS & _). exact LS. Qed.
(* m->n *)
Lemma s6_rd_n : forall m mc, sa_mconf rd m mc -> rd32 rd (m + seg_spec.MC_N) (Z.of_nat (length (mc_seg mc))).
Proof.
intros m mc (bs & HB & E). pose proof E as (L & LS & _ & (N0 & HN) & _).
unfold seg_spec.SEG_M_SIZE in L. unfold seg_spec.fldz in HN. change (Z.to_nat 4) with 4%nat in HN.
replace (m + seg_spec.MC_N) with (m + Z.of_nat (Z.to_nat seg_spec.MC_N)) by (unfold seg_spec.MC_N; lia).
apply (s6_rd32_of rd m bs (Z.to_nat seg_spec.MC_N)); [exact HB | unfold seg_spec.MC_N; lia | exact HN | lia].
Qed.
(* a 4-byte field of m->seg[i] *)
Lemma s6_rd_seg4 : forall m mc bs i off v, sa_bytes rd m bs -> seg_spec.mconf_enc mc bs ->
  (i < length (mc_seg mc))%nat -> (off + 4 <= 256)%nat ->
  seg_spec.fld off 4 (seg_spec.fld (256 * i) 256 bs) = Mem.le4 (Z_to_bv 64 v) -> 0 <= v < 2 ^ 32 ->
  rd32 rd (m + 256 * Z.of_nat i + Z.of_nat off) v.
Proof.
intros m mc bs i off v HB E Hi Ho Hf Hv. pose proof E as (L & LS & _).
unfold seg_spec.SEG_M_SIZE in L.
replace (m + 256 * Z.of_nat i + Z.of_nat off) with (m + Z.of_nat (256 * i + off)) by lia.
apply (s6_rd32_of rd m bs (256 * i + off)); [exact HB | lia | | exact Hv].
rewrite <- Hf. apply nth_error_ext. intros j. rewrite !s6_nth_error_fld.
destruct (Nat.ltb_spec0 j 4); [|reflexivity].
destruct (Nat.ltb_spec0 (off + j) 256); [|lia]. f_equal. lia.
Qed.
Lemma s6_rd_role_set : forall m mc i, sa_mconf rd m mc -> (i < length (mc_seg mc))%nat ->
  rd32 rd (m + 256 * Z.of_nat i + 20) (seg_spec.b2z (ms_role_set (nth i (mc_seg mc) mseg_d))).
Proof.
intros m mc i (bs & HB & E) Hi. pose proof E as (_ & _ & SG & _).
destruct (SG i Hi) as (_ & _ & _ & RS & _). unfold seg_spec.flag_enc, seg_spec.fldz, seg_spec.MS_ROLE_SET in RS.
change 20 with (Z.of_nat 20). apply (s6_rd_seg4 m mc bs i 20); [exact HB | exact E | exact Hi | lia | | ].
- exact RS.
- destruct (ms_role_set _); cbn; lia.
Qed.
Lemma s6_rd_model_set : forall m mc i, sa_mconf rd m mc -> (i < length (mc_seg mc))%nat ->
  rd32 rd (m + 256 * Z.of_nat i + 32) (seg_spec.b2z (ms_model_set (nth i (mc_seg mc) mseg_d))).
Proof.
intros m mc i (bs & HB & E) Hi. pose proof E as (_ & _ & SG & _).
destruct (SG i Hi) as (_ & _ & _ & _ & _ & _ & MS & _).
unfold seg_spec.flag_enc, seg_spec.fldz, seg_spec.MS_MODEL_SET in MS.
change 32 with (Z.of_nat 32). apply (s6_rd_seg4 m mc bs i 32); [exact HB | exact E | exact Hi | lia | | ].
- exact MS.
- destruct (ms_model_set _); cbn; lia.
Qed.
Lemma s6_rd_role : forall m mc i, sa_mconf rd m mc -> (i < length (mc_seg mc))%nat ->
  0 <= ms_role (nth i (mc_seg mc) mseg_d) < 2 ^ 31 /\
  rd32 rd (m + 256 * Z.of_nat i + 16) (ms_role (nth i (mc_seg mc) mseg_d)).
Proof.
intros m mc i (bs & HB & E) Hi. pose proof E as (_ & _ & SG & _).
destruct (SG i Hi) as (_ & _ & ((R0 & RE) & R31) & _). unfold seg_spec.fldz, seg_spec.MS_ROLE in RE.
split; [lia|].
change 16 with (Z.of_nat 16). apply (s6_rd_seg4 m mc bs i 16); [exact HB | exact E | exact Hi | lia | exact RE | lia].
Qed.
End r.

(* the stores of c:303 and c:306-307, through the reader: rd' is rd but on the stored word(s), which hold 0 *)
Lemma s6_sa_bytes_upd : forall (rd rd' : reader) a bs o X,
  sa_bytes rd a bs -> (o + length X <= length bs)%nat ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> ~ (a + Z.of_nat o <= x < a + Z.of_nat (o + length X)) -> rd' x = rd x) ->
  (forall j, (j < length X)%nat -> rd' (a + Z.of_nat (o + j)) = Some (bv_unsigned (nth j X ZB0))) ->
  sa_bytes rd' a (Mem.upd_bytes bs o X).
Proof.
intros rd rd' a bs o X HB Hl Hout Hin j Hj. rewrite Mem.upd_bytes_length in Hj by exact Hl.
assert (En : forall (l : list byte) i, (i < length l)%nat -> nth i l ZB0 = match nth_error l i with Some b => b | None => ZB0 end).
{ intros l i Hi. destruct (nth_error l i) as [b|] eqn:Eb; [exact (nth_error_nth l i ZB0 Eb)|].
  apply nth_error_None in Eb. lia. }
rewrite (En (Mem.upd_bytes bs o X) j) by (rewrite Mem.upd_bytes_length by exact Hl; exact Hj).
rewrite (s6_nth_upd bs X o j Hl).
destruct (Nat.leb_spec0 o j), (Nat.ltb_spec0 j (o + length X)); cbn [andb].
- replace j with (o + (j - o))%nat at 1 by lia. rewrite (Hin (j - o)%nat) by lia.
  rewrite (En X (j - o)%nat) by lia. reflexivity.
- rewrite Hout by lia. rewrite (HB j Hj). rewrite (En bs j) by exact Hj. reflexivity.
- rewrite Hout by lia. rewrite (HB j Hj). rewrite (En bs j) by exact Hj. reflexivity.
- rewrite Hout by lia. rewrite (HB j Hj). rewrite (En bs j) by exact Hj. reflexivity.
Qed.
Lemma s6_Z4_byte : forall j, (j < 4)%nat -> bv_unsigned (nth j s6_Z4 ZB0) = 0.
Proof. intros j Hj. destruct j as [|[|[|[|j]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]. Qed.
Lemma s6_store_drop_model : forall (rd rd' : reader) m mc i,
  sa_mconf rd m mc -> (i < length (mc_seg mc))%nat ->
  (forall x, m <= x < m + 9236 -> ~ (m + 256 * Z.of_nat i + 32 <= x < m + 256 * Z.of_nat i + 36) -> rd' x = rd x) ->
  rd32 rd' (m + 256 * Z.of_nat i + 32) 0 ->
  sa_mconf rd' m (m_upd mc i ms_drop_model).
Proof.
intros rd rd' m mc i (bs & HB & E) Hi Hout Hz. pose proof E as (L & LS & SG & _).
unfold seg_spec.SEG_M_SIZE in L.
exists (Mem.upd_bytes bs (256 * i + 32) s6_Z4). split.
- apply (s6_sa_bytes_upd rd rd' m bs (256 * i + 32) s6_Z4 HB); [rewrite s6_Z4_len; lia | |].
  + intros x Hx1 Hx. apply Hout; [lia|]. rewrite s6_Z4_len in Hx. lia.
  + intros j Hj. rewrite s6_Z4_len in Hj. rewrite s6_Z4_byte by exact Hj.
    replace (m + Z.of_nat (256 * i + 32 + j)) with (m + 256 * Z.of_nat i + 32 + Z.of_nat j) by lia.
    rewrite (Hz j Hj). f_equal. unfold le_byte. rewrite Z.mod_0_l by (cbn; lia). rewrite Z.shiftr_0_l. reflexivity.
- apply s6_mconf_upd; [exact E | exact Hi | rewrite s6_Z4_len; lia |].
  apply s6_mseg_drop_model. exact (SG i Hi).
Qed.
Lemma s6_store_drop_role : forall (rd rd' : reader) m mc i,
  sa_mconf rd m mc -> (i < length (mc_seg mc))%nat ->
  (forall x, m <= x < m + 9236 -> ~ (m + 256 * Z.of_nat i + 16 <= x < m + 256 * Z.of_nat i + 24) -> rd' x = rd x) ->
  rd32 rd' (m + 256 * Z.of_nat i + 16) 0 -> rd32 rd' (m + 256 * Z.of_nat i + 20) 0 ->
  sa_mconf rd' m (m_upd mc i ms_drop_role).
Proof.
intros rd rd' m mc i (bs & HB & E) Hi Hout Hz1 Hz2. pose proof E as (L & LS & SG & _).
unfold seg_spec.SEG_M_SIZE in L.
exists (Mem.upd_bytes bs (256 * i + 16) (s6_Z4 ++ s6_Z4)). split.
- apply (s6_sa_bytes_upd rd rd' m bs (256 * i + 16) (s6_Z4 ++ s6_Z4) HB); [rewrite length_app, s6_Z4_len; lia | |].
  + intros x Hx1 Hx. apply Hout; [lia|]. rewrite length_app, s6_Z4_len in Hx. lia.
  + intros j Hj. rewrite length_app, s6_Z4_len in Hj.
    destruct (Nat.lt_ge_cases j 4) as [J|J].
    * rewrite app_nth1 by (rewrite s6_Z4_len; exact J). rewrite s6_Z4_byte by exact J.
      replace (m + Z.of_nat (256 * i + 16 + j)) with (m + 256 * Z.of_nat i + 16 + Z.of_nat j) by lia.
      rewrite (Hz1 j J). f_equal. unfold le_byte. rewrite Z.mod_0_l by (cbn; lia). rewrite Z.shiftr_0_l. reflexivity.
    * rewrite app_nth2 by (rewrite s6_Z4_len; exact J). rewrite s6_Z4_len.
      rewrite s6_Z4_byte by lia.
      replace (m + Z.of_nat (256 * i + 16 + j)) with (m + 256 * Z.of_nat i + 20 + Z.of_nat (j - 4)) by lia.
      rewrite (Hz2 (j - 4)%nat ltac:(lia)). f_equal. unfold le_byte. rewrite Z.mod_0_l by (cbn; lia).
      rewrite Z.shiftr_0_l. reflexivity.
- apply s6_mconf_upd; [exact E | exact Hi | rewrite length_app, s6_Z4_len; lia |].
  apply s6_mseg_drop_role. exact (SG i Hi).
Qed.
(* m_refuse keeps the table *)
Lemma s6_refuse_seg : forall c l k, mc_seg (m_refuse c l k) = mc_seg c.
Proof. reflexivity. Qed.
(* one pass, by the entry's two flags (and its role when role_set is 1) *)
Lemma s6_seg_00 : forall c i, ms_role_set (nth i (mc_seg c) mseg_d) = false ->
  ms_model_set (nth i (mc_seg c) mseg_d) = false -> m_cross_seg c i = c.
Proof. intros c i H1 H2. unfold m_cross_seg. rewrite H1, H2. reflexivity. Qed.
Lemma s6_seg_01 : forall c i, ms_role_set (nth i (mc_seg c) mseg_d) = false ->
  ms_model_set (nth i (mc_seg c) mseg_d) = true -> m_cross_seg c i = m_upd (m_refuse c 0 false) i ms_drop_model.
Proof. intros c i H1 H2. unfold m_cross_seg. rewrite H1, H2. reflexivity. Qed.
Lemma s6_seg_10 : forall c i, ms_role_set (nth i (mc_seg c) mseg_d) = true ->
  ms_model_set (nth i (mc_seg c) mseg_d) = false ->
  m_cross_seg c i = if ms_role (nth i (mc_seg c) mseg_d) =? 4 then m_upd (m_refuse c 0 false) i ms_drop_role else c.
Proof.
intros c i H1 H2. unfold m_cross_seg. rewrite H1, H2. cbn [andb negb].
destruct (ms_role (nth i (mc_seg c) mseg_d) =? 4); reflexivity.
Qed.
Lemma s6_seg_11 : forall c i, ms_role_set (nth i (mc_seg c) mseg_d) = true ->
  ms_model_set (nth i (mc_seg c) mseg_d) = true ->
  m_cross_seg c i = if ms_role (nth i (mc_seg c) mseg_d) =? 4 then c else m_upd (m_refuse c 0 false) i ms_drop_model.
Proof.
intros c i H1 H2. unfold m_cross_seg. rewrite H1, H2. cbn [andb negb].
destruct (ms_role (nth i (mc_seg c) mseg_d) =? 4); reflexivity.
Qed.

(* the payload decodes to 1 .. 4 files (decode: 1 + b2 mod 4), so the last turn f has f <= 3 *)
Lemma s6_dec_files_len : forall k inp, length (dec_files k inp) = k.
Proof.
induction k as [|k IH]; intros inp; cbn [dec_files]; [reflexivity|].
destruct (fuzz_u8 inp) as [lb i1]. destruct (fuzz_u16 i1) as [len i2]. destruct (fuzz_take i2 len) as [p i3].
cbn [length]. rewrite IH. reflexivity.
Qed.
Lemma s6_nfiles_range : forall pl, 1 <= seg_spec.seg_nfiles pl <= 4.
Proof.
intros pl. unfold seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay, decode.
destruct (fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1].
destruct (fuzz_u8 i1) as [fl i2]. destruct (fuzz_u8 i2) as [b2 i3].
cbn [p_files]. rewrite s6_dec_files_len.
pose proof (Z.mod_pos_bound b2 4 ltac:(lia)) as H. rewrite Z2Nat.id by lia. lia.
Qed.
