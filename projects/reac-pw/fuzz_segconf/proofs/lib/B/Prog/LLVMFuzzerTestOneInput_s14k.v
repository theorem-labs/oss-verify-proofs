(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: lemmas the segments of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command) share: the live bytes the recorder owns, the payload bytes and the stack kept along the walk's journal, the events and meter left (non-negative; each callee's meter at most its events times one unit), the joined size of a message's words (words_acc_need copied from fuzz_command's plain lib/Prog/SlotRec.v); in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh7.v and ACh8.v (the keep lemmas of cgif_close's segments). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s01.v, with its module paths and module names changed; 709 of its 809 lines of code are new or changed and 276 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the kit of the walk
   of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segment S04 (K85110 f -> K85210 f,
   0x85110 .. 0x8520c), LLVMFuzzerTestOneInput_s14.v.

   - The turn's bytes at the cursor (the pure part): the cursor seg_cur pl f is a suffix of the input, its bytes are
     the payload's at x_cur, file f is read at it, and its four shapes (0, 1, 2, 3 or more bytes) give lb, the u16
     length, the bytes fuzz_take takes and the text's length; memchr's first zero is the text's length. The form
     and the names are the image-B owner's UBSan walk of the same code (lib/U/Prog/Seg/L01.v:39-271, the l01 lemmas),
     restated over image B's readers.
   - The walk's own points: the image facts carried to a later reader (image A's S00 walk's s10_lt_img_kept, the
     facts from IMGF's fields; the stack guard's .got word re-read from AR at the new state by
     SegRecCells.seg_rec_cells), the facts of a point after one allocator call (image A's S01 / S02 kit
     LLVMFuzzerTestOneInput_s12k.v lk_after_alloc / lt_malloc_at, image A's S01 / S02 commit 119b28fad68f, with
     image B's frame: the shadow base at 200(s1), SH(FR) at 184(s1)), the memchr wrapper's call step
     (MemchrDef.amemchr_realizesM through PaArt.aj_art_at, as fuzz_command's lib/B/Prog/LLVMFuzzerTestOneInput_s41.v
     aw_strnlen_loc, origin/ossv/recipes 3abc3740de97; its constants window from IMGF's cif_snl_rom and
     SegRecBase.seg_snl_unowned), and the three inner cut points of S04.
   Statement text and proofs only about the walk's own points: no other function of the binary is proved here. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YP03.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaCall PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegRo SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegRecCells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require MemchrDef ConstsViewDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* every lemma below takes all its Section's variables and hypotheses, in their order, so the segment file passes
   one fixed argument list *)
Set Default Proof Using "All".

(* ============================== the turn's bytes at the cursor (pure) ============================== *)
(* s is a suffix of l (l01_sfx) *)
Definition k14_sfx (s l : list Z) : Prop := exists pre, l = pre ++ s.
Lemma k14_sfx_refl : forall l, k14_sfx l l.
Proof. intros l. exists []. reflexivity. Qed.
Lemma k14_sfx_trans : forall a b c, k14_sfx a b -> k14_sfx b c -> k14_sfx a c.
Proof. intros a b c (p1 & ->) (p2 & ->). exists (p2 ++ p1). rewrite app_assoc. reflexivity. Qed.
Lemma k14_sfx_u8 : forall l, k14_sfx (snd (SegModel.fuzz_u8 l)) l.
Proof. intros [|b l]; cbn [SegModel.fuzz_u8 snd]; [exists []; reflexivity | exists [b]; reflexivity]. Qed.
Lemma k14_sfx_u16 : forall l, k14_sfx (snd (SegModel.fuzz_u16 l)) l.
Proof.
intros l. unfold SegModel.fuzz_u16.
pose proof (k14_sfx_u8 l) as H1. revert H1. destruct (SegModel.fuzz_u8 l) as [lo i1]. cbn [snd]. intros H1.
pose proof (k14_sfx_u8 i1) as H2. revert H2. destruct (SegModel.fuzz_u8 i1) as [hi i2]. cbn [snd]. intros H2.
exact (k14_sfx_trans _ _ _ H2 H1).
Qed.
Lemma k14_sfx_take : forall l n, k14_sfx (snd (SegModel.fuzz_take l n)) l.
Proof.
intros l n. cbv beta zeta delta [SegModel.fuzz_take]. cbn [snd].
exists (firstn (Nat.min (Z.to_nat n) (length l)) l). symmetry. apply firstn_skipn.
Qed.
Lemma k14_sfx_skip : forall k l, k14_sfx (seg_spec.seg_skip k l) l.
Proof.
induction k as [|k IH]; intros l; cbn [seg_spec.seg_skip]; [apply k14_sfx_refl|].
pose proof (k14_sfx_u8 l) as H1. revert H1. destruct (SegModel.fuzz_u8 l) as [lb i1]. cbn [snd]. intros H1.
pose proof (k14_sfx_u16 i1) as H2. revert H2. destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [snd]. intros H2.
pose proof (k14_sfx_take i2 len) as H3. revert H3. destruct (SegModel.fuzz_take i2 len) as [q i3]. cbn [snd].
intros H3.
exact (k14_sfx_trans _ _ _ (IH i3) (k14_sfx_trans _ _ _ H3 (k14_sfx_trans _ _ _ H2 H1))).
Qed.
(* the cursor after k records is a suffix of the input *)
Lemma k14_cur_sfx : forall pl k, k14_sfx (seg_spec.seg_cur pl k) (seg_spec.seg_in pl).
Proof.
intros pl k. unfold seg_spec.seg_cur, seg_spec.seg_hdr.
eapply k14_sfx_trans; [apply k14_sfx_skip|].
eapply k14_sfx_trans; [apply k14_sfx_u8|].
eapply k14_sfx_trans; [apply k14_sfx_u8|].
apply k14_sfx_u8.
Qed.
Lemma k14_skipn_zs : forall k (l : list byte), skipn k (seg_spec.zs l) = seg_spec.zs (skipn k l).
Proof. unfold seg_spec.zs. induction k as [|k IH]; intros [|b l]; cbn [skipn map]; try reflexivity. apply IH. Qed.
Lemma k14_zs_len : forall l : list byte, length (seg_spec.zs l) = length l.
Proof. intros l. unfold seg_spec.zs. apply length_map. Qed.
Lemma k14_skipn_pre : forall (pre s : list Z), skipn (length pre) (pre ++ s) = s.
Proof. induction pre as [|x pre IH]; intros s; [reflexivity|]. cbn [length app skipn]. apply IH. Qed.
(* a suffix of the input's bytes is the zs of the input's last length s bytes *)
Lemma k14_sfx_bytes : forall (pl : list byte) s, k14_sfx s (seg_spec.zs pl) ->
  (length s <= length pl)%nat /\ seg_spec.zs (skipn (length pl - length s) pl) = s.
Proof.
intros pl s (pre & E).
assert (HL : length pl = (length pre + length s)%nat).
{ rewrite <- (k14_zs_len pl), E, length_app. reflexivity. }
split; [lia|].
replace (length pl - length s)%nat with (length pre) by lia.
rewrite <- k14_skipn_zs, E. apply k14_skipn_pre.
Qed.
(* byte i of the cursor is byte |pl| - |cur| + i of the input *)
Lemma k14_cur_nth : forall pl f i, (i < length (seg_spec.seg_cur pl f))%nat ->
  (length (seg_spec.seg_cur pl f) <= length pl)%nat /\
  nth i (seg_spec.seg_cur pl f) 0 =
  bv_unsigned (nth (length pl - length (seg_spec.seg_cur pl f) + i) pl (Z_to_bv 8 0)).
Proof.
intros pl f i Hi.
destruct (k14_sfx_bytes pl (seg_spec.seg_cur pl f) (k14_cur_sfx pl f)) as [HL E].
split; [exact HL|].
transitivity (nth i (seg_spec.zs (skipn (length pl - length (seg_spec.seg_cur pl f)) pl)) 0); [rewrite E; reflexivity|].
unfold seg_spec.zs.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, length_skipn; lia).
rewrite map_nth, nth_skipn. reflexivity.
Qed.
(* every byte of the cursor is a byte *)
Lemma k14_cur_bytes : forall pl f, Forall (fun z => 0 <= z < 256) (seg_spec.seg_cur pl f).
Proof.
intros pl f. destruct (k14_cur_sfx pl f) as (pre & E).
assert (HA : Forall (fun z => 0 <= z < 256) (seg_spec.seg_in pl)).
{ unfold seg_spec.seg_in, seg_spec.zs. apply Forall_map. apply Forall_forall. intros b _.
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
rewrite E in HA. apply Forall_app in HA. exact (proj2 HA).
Qed.

(* the file records: dec_files k l has k entries, the f-th read at the cursor after f records (l01_dec_len /
   l01_dec_nth) *)
Lemma k14_dec_len : forall k l, length (SegModel.dec_files k l) = k.
Proof.
induction k as [|k IH]; intros l; cbn [SegModel.dec_files]; [reflexivity|].
destruct (SegModel.fuzz_u8 l) as [lb i1]. destruct (SegModel.fuzz_u16 i1) as [len i2].
destruct (SegModel.fuzz_take i2 len) as [q i3]. cbn [length]. rewrite IH. reflexivity.
Qed.
Lemma k14_dec_nth : forall f k l, (f < k)%nat ->
  nth f (SegModel.dec_files k l) (SegModel.File 0 []) =
  SegModel.File (fst (SegModel.fuzz_u8 (seg_spec.seg_skip f l)))
    (SegModel.fuzz_str (fst (SegModel.fuzz_take (snd (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 (seg_spec.seg_skip f l)))))
                         (fst (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 (seg_spec.seg_skip f l)))))))).
Proof.
induction f as [|f IH]; intros k l Hf; (destruct k as [|k]; [lia|]); cbn [SegModel.dec_files seg_spec.seg_skip].
- destruct (SegModel.fuzz_u8 l) as [lb i1]; cbn [fst snd].
  destruct (SegModel.fuzz_u16 i1) as [len i2]; cbn [fst snd].
  destruct (SegModel.fuzz_take i2 len) as [q i3]; cbn [fst snd nth]. reflexivity.
- destruct (SegModel.fuzz_u8 l) as [lb i1]; cbn [fst snd].
  destruct (SegModel.fuzz_u16 i1) as [len i2]; cbn [fst snd].
  destruct (SegModel.fuzz_take i2 len) as [q i3]; cbn [fst snd nth]. apply IH. lia.
Qed.
Lemma k14_files : forall pl, seg_spec.seg_files pl =
  SegModel.dec_files (Z.to_nat (1 + fst (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8
    (seg_spec.seg_in pl)))))) mod 4)) (seg_spec.seg_hdr pl).
Proof.
intros pl. unfold seg_spec.seg_files, seg_spec.seg_pay, SegModel.decode, seg_spec.seg_hdr.
destruct (SegModel.fuzz_u8 (seg_spec.seg_in pl)) as [b0 i1]; cbn [fst snd].
destruct (SegModel.fuzz_u8 i1) as [fl i2]; cbn [fst snd].
destruct (SegModel.fuzz_u8 i2) as [b2 i3]; cbn [fst snd SegModel.p_files]. reflexivity.
Qed.

(* turn f's reads at the cursor: lb, the u16 length, the bytes left after them, the bytes fuzz_take takes and their
   count, and the text's length (the taken bytes cut at their first NUL) *)
Definition k14_lb (l : list Z) : Z := fst (SegModel.fuzz_u8 l).
Definition k14_tl (l : list Z) : list Z := snd (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))).
Definition k14_len (l : list Z) : Z := fst (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))).
Definition k14_take (l : list Z) : list Z := fst (SegModel.fuzz_take (k14_tl l) (k14_len l)).
Definition k14_n (l : list Z) : Z := Z.of_nat (length (SegModel.cut_nul (k14_take l))).

Lemma k14_file : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  seg_spec.seg_file pl f =
  SegModel.File (k14_lb (seg_spec.seg_cur pl f)) (SegModel.fuzz_str (k14_take (seg_spec.seg_cur pl f))).
Proof.
intros pl f Hf. unfold seg_spec.seg_nfiles in Hf.
unfold seg_spec.seg_file, k14_lb, k14_take, k14_tl, k14_len, seg_spec.seg_cur.
rewrite k14_files in Hf |- *. apply k14_dec_nth. rewrite k14_dec_len in Hf. lia.
Qed.
Lemma k14_lb_eq : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl -> seg_spec.seg_lb pl f = k14_lb (seg_spec.seg_cur pl f).
Proof. intros pl f Hf. unfold seg_spec.seg_lb. rewrite (k14_file pl f Hf). reflexivity. Qed.
Lemma k14_txt_eq : forall pl f, Z.of_nat f < seg_spec.seg_nfiles pl ->
  seg_spec.seg_txt_n pl f = k14_n (seg_spec.seg_cur pl f).
Proof. intros pl f Hf. unfold seg_spec.seg_txt_n, seg_spec.seg_txt. rewrite (k14_file pl f Hf). reflexivity. Qed.
Lemma k14_np_eq : forall pl f, seg_spec.seg_turn_np pl f = Z.of_nat (length (k14_take (seg_spec.seg_cur pl f))).
Proof. reflexivity. Qed.
Lemma k14_tl_eq : forall pl f, seg_spec.seg_turn_tail pl f = k14_tl (seg_spec.seg_cur pl f).
Proof. reflexivity. Qed.

(* the text is at most the taken bytes, at most 65535 *)
Lemma k14_n_le : forall l, 0 <= k14_n l <= Z.of_nat (length (k14_take l)) /\ Z.of_nat (length (k14_take l)) <= 65535.
Proof.
intros l. unfold k14_n.
pose proof (SegModel.cut_nul_len (k14_take l)) as H1.
assert (H2 : (length (k14_take l) <= Z.to_nat (k14_len l))%nat).
{ unfold k14_take. cbv beta zeta delta [SegModel.fuzz_take]. cbn [fst]. rewrite length_firstn. lia. }
assert (H3 : 0 <= k14_len l <= 65535).
{ unfold k14_len, SegModel.fuzz_u16. destruct (SegModel.fuzz_u8 (snd (SegModel.fuzz_u8 l))) as [lo i1].
  destruct (SegModel.fuzz_u8 i1) as [hi i2]. cbn [fst]. apply SegModel.land65535. }
lia.
Qed.
(* the bytes left after the turn's header are a suffix of the input, and the taken bytes are at most them *)
Lemma k14_tail_len : forall pl f,
  (length (k14_tl (seg_spec.seg_cur pl f)) <= length (seg_spec.seg_cur pl f) <= length pl)%nat /\
  (length (k14_take (seg_spec.seg_cur pl f)) <= length (k14_tl (seg_spec.seg_cur pl f)))%nat.
Proof.
intros pl f.
destruct (k14_sfx_bytes pl (seg_spec.seg_cur pl f) (k14_cur_sfx pl f)) as [HL _].
assert (Ht : k14_sfx (k14_tl (seg_spec.seg_cur pl f)) (seg_spec.seg_cur pl f)).
{ unfold k14_tl. exact (k14_sfx_trans _ _ _ (k14_sfx_u16 _) (k14_sfx_u8 _)). }
destruct Ht as (pre & E). assert (HT : length (seg_spec.seg_cur pl f) = (length pre + length (k14_tl (seg_spec.seg_cur pl f)))%nat)
  by (rewrite E at 1; rewrite length_app; reflexivity).
split; [lia|].
unfold k14_take. cbv beta zeta delta [SegModel.fuzz_take]. cbn [fst]. rewrite length_firstn. lia.
Qed.
Lemma k14_nth_firstn : forall {A} (l : list A) h i d, (i < h)%nat -> nth i (firstn h l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros h i d Hi.
- destruct h; reflexivity.
- destruct h as [|h]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
(* byte i of the taken bytes is byte |l| - |tail| + i of the cursor *)
Lemma k14_take_nth : forall l i, (i < length (k14_take l))%nat ->
  nth i (k14_take l) 0 = nth (length l - length (k14_tl l) + i) l 0.
Proof.
intros l i Hi.
assert (Ht : k14_sfx (k14_tl l) l) by (unfold k14_tl; exact (k14_sfx_trans _ _ _ (k14_sfx_u16 _) (k14_sfx_u8 _))).
destruct Ht as (pre & E).
assert (HL : length l = (length pre + length (k14_tl l))%nat) by (rewrite E at 1; rewrite length_app; reflexivity).
unfold k14_take in *. cbv beta zeta delta [SegModel.fuzz_take] in *. cbn [fst] in *.
rewrite length_firstn in Hi. rewrite k14_nth_firstn by lia.
replace (length l - length (k14_tl l) + i)%nat with (length pre + i)%nat by lia.
transitivity (nth (length pre + i) (pre ++ k14_tl l) 0).
- rewrite app_nth2 by lia. f_equal. lia.
- rewrite <- E. reflexivity.
Qed.

(* the four shapes of the cursor's bytes *)
Lemma k14_take_nil : forall l, k14_tl l = [] -> k14_take l = [].
Proof.
intros l H. unfold k14_take. rewrite H. cbv beta zeta delta [SegModel.fuzz_take]. cbn [fst]. apply firstn_nil.
Qed.
Lemma k14_shape0 : k14_lb [] = 0 /\ k14_tl [] = [] /\ k14_take [] = [] /\ k14_n [] = 0.
Proof. repeat split; reflexivity. Qed.
Lemma k14_shape1 : forall b0, k14_lb [b0] = b0 /\ k14_tl [b0] = [] /\ k14_take [b0] = [] /\ k14_n [b0] = 0.
Proof. intros b0. repeat split; reflexivity. Qed.
Lemma k14_shape2 : forall b0 b1,
  k14_lb [b0; b1] = b0 /\ k14_tl [b0; b1] = [] /\ k14_take [b0; b1] = [] /\ k14_n [b0; b1] = 0.
Proof.
intros b0 b1. assert (E : k14_take [b0; b1] = []) by (apply k14_take_nil; reflexivity).
unfold k14_n. rewrite E. repeat split; reflexivity.
Qed.
(* lo | hi << 8 for two bytes: lo + 256 hi (checked on the 65536 pairs, l01_lor) *)
Lemma k14_lor_all : forallb (fun lo => forallb (fun hi => Z.lor lo (Z.shiftl hi 8) =? lo + hi * 256)
    (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma k14_lor : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor lo (Z.shiftl hi 8) = lo + hi * 256.
Proof.
intros lo hi Hlo Hhi. pose proof k14_lor_all as H.
rewrite forallb_forall in H.
assert (Hl : In lo (map Z.of_nat (seq 0 256))).
{ apply in_map_iff. exists (Z.to_nat lo). split; [lia|]. apply in_seq. lia. }
specialize (H lo Hl). rewrite forallb_forall in H.
assert (Hh : In hi (map Z.of_nat (seq 0 256))).
{ apply in_map_iff. exists (Z.to_nat hi). split; [lia|]. apply in_seq. lia. }
apply Z.eqb_eq. exact (H hi Hh).
Qed.
Lemma k14_shape3 : forall b0 b1 b2 r, 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  k14_lb (b0 :: b1 :: b2 :: r) = b0 /\ k14_tl (b0 :: b1 :: b2 :: r) = r /\
  k14_take (b0 :: b1 :: b2 :: r) = firstn (Nat.min (Z.to_nat (b1 + b2 * 256)) (length r)) r.
Proof.
intros b0 b1 b2 r H1 H2. split; [reflexivity|]. split; [reflexivity|].
unfold k14_take, k14_tl, k14_len, SegModel.fuzz_u16. cbn [SegModel.fuzz_u8 fst snd].
rewrite (k14_lor b1 b2 H1 H2).
replace (Z.land (b1 + b2 * 256) 65535) with (b1 + b2 * 256).
- reflexivity.
- change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia.
Qed.

(* the text's length is the index of the first NUL of the taken bytes, or their count: what memchr(P1, 0, NP)
   answers (first_byte, as fuzz_command's _s41.v aw_first_nul_loc) *)
Lemma k14_first_nul : forall (rd : Z -> option Z) x (t : list Z) k,
  (forall i, (i < length t)%nat -> rd (x + Z.of_nat i) = Some (nth i t 0)) ->
  0 <= k <= Z.of_nat (length t) ->
  (forall i, 0 <= i < k -> exists b, rd (x + i) = Some b /\ b <> 0) ->
  (k < Z.of_nat (length t) -> rd (x + k) = Some 0) ->
  k = Z.of_nat (length (SegModel.cut_nul t)).
Proof.
intros rd x t. revert x. induction t as [|b t IH]; intros x k Ht Hk Hnz Hz.
- cbn [length SegModel.cut_nul] in *. lia.
- cbn [SegModel.cut_nul].
  destruct (Z.eqb_spec b 0) as [Hb | Hb].
  + cbn [length]. destruct (Z.eq_dec k 0) as [-> | Hk0]; [reflexivity|].
    exfalso. destruct (Hnz 0 ltac:(lia)) as (b' & Hb' & Hne).
    pose proof (Ht 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0. rewrite Z.add_0_r in Hb', H0.
    rewrite Hb' in H0. injection H0 as ->. contradiction.
  + cbn [length]. rewrite Nat2Z.inj_succ.
    assert (Hk1 : 1 <= k).
    { destruct (Z.eq_dec k 0) as [-> | Hk0]; [|lia]. exfalso.
      pose proof (Hz ltac:(cbn [length]; lia)) as H0. pose proof (Ht 0%nat ltac:(cbn [length]; lia)) as H1.
      cbn [nth] in H1. rewrite Z.add_0_r in H0, H1. rewrite H0 in H1. injection H1 as <-. contradiction. }
    assert (E : k - 1 = Z.of_nat (length (SegModel.cut_nul t))).
    { apply (IH (x + 1)).
      - intros i Hi. replace (x + 1 + Z.of_nat i) with (x + Z.of_nat (Datatypes.S i)) by lia.
        exact (Ht (Datatypes.S i) ltac:(cbn [length]; lia)).
      - cbn [length] in Hk. lia.
      - intros i Hi. replace (x + 1 + i) with (x + (i + 1)) by lia. apply Hnz. lia.
      - intros Hlt. replace (x + 1 + (k - 1)) with (x + k) by lia. apply Hz. cbn [length]. lia. }
    lia.
Qed.

(* ============================== lists, words, registers ============================== *)
(* blocks_bytes is the sum of the live blocks' sizes (image A's lk_bsum) *)
Fixpoint k14_bsum (bl : list (Z * Z)) : Z := match bl with [] => 0 | b :: l => snd b + k14_bsum l end.
Lemma k14_bsum_app : forall l1 l2, k14_bsum (l1 ++ l2) = k14_bsum l1 + k14_bsum l2.
Proof. induction l1 as [|b l IH]; intros l2; cbn [k14_bsum app]; [reflexivity | rewrite IH; ring]. Qed.
Lemma k14_bsum_perm : forall l1 l2, Permutation l1 l2 -> k14_bsum l1 = k14_bsum l2.
Proof. intros l1 l2 H. induction H; cbn [k14_bsum]; [reflexivity | rewrite IHPermutation; reflexivity | ring | congruence]. Qed.
(* a callee-saved register a call keeps *)
Lemma k14_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* a word every byte of which two readers agree on *)
Lemma k14_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
(* a word all of whose bytes some reader shows (image A's s10_rdword_some) *)
Lemma k14_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) ->
  exists v, rdword rd a = Some v.
Proof.
intros rd a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
pose proof (H 1 ltac:(lia)) as H1. pose proof (H 2 ltac:(lia)) as H2. pose proof (H 3 ltac:(lia)) as H3.
pose proof (H 4 ltac:(lia)) as H4. pose proof (H 5 ltac:(lia)) as H5. pose proof (H 6 ltac:(lia)) as H6.
pose proof (H 7 ltac:(lia)) as H7.
destruct (rd a) as [b0|]; [|congruence]. destruct (rd (a + 1)) as [b1|]; [|congruence].
destruct (rd (a + 2)) as [b2|]; [|congruence]. destruct (rd (a + 3)) as [b3|]; [|congruence].
destruct (rd (a + 4)) as [b4|]; [|congruence]. destruct (rd (a + 5)) as [b5|]; [|congruence].
destruct (rd (a + 6)) as [b6|]; [|congruence]. destruct (rd (a + 7)) as [b7|]; [|congruence].
eexists; reflexivity.
Qed.
(* the C bytes of a block, read by a reader that agrees on them (lt_cm's two encodings) *)
Lemma k14_bytes_kept : forall (rd rd' : reader) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> rd' x = rd x) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma k14_cm_kept : forall (rd rd' : reader) c m st,
  (forall x, c <= x < c + seg_spec.SEG_C_SIZE -> rd' x = rd x) ->
  (forall x, m <= x < m + seg_spec.SEG_M_SIZE -> rd' x = rd x) ->
  lt_cm rd c m st -> lt_cm rd' c m st.
Proof.
intros rd rd' c m st Kc Km ((bc & Hbc & Ec) & (bm & Hbm & Em)). split.
- exists bc. split; [|exact Ec]. apply (k14_bytes_kept rd); [|exact Hbc].
  destruct Ec as (Hl & _). intros x Hx. apply Kc. lia.
- exists bm. split; [|exact Em]. apply (k14_bytes_kept rd); [|exact Hbm].
  destruct Em as (Hl & _). intros x Hx. apply Km. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma k14_slots_kept : forall cx (rd rd' : reader) L,
  (forall o v, In (o, v) L -> forall x, x_s1 cx + o <= x < x_s1 cx + o + 8 -> rd' x = rd x) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L HK H o v Hin. apply (k14_word_kept rd); [|exact (H o v Hin)]. intros x Hx. exact (HK o v Hin x Hx).
Qed.

Lemma k14_blocks_bytes : forall B ly S, blocks_bytes S = k14_bsum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, ablocks, blocks. induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc c); cbn [map k14_bsum snd fst]; [rewrite IH; reflexivity | exact IH].
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma k14_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* a ROM byte is shown by every reader (image A's s10_rom_view_some) *)
Lemma k14_rom_view_some : forall (H : word -> bool) mem a, seg_rom SEGS (Z_to_bv 64 a) <> None -> aview SEGS H mem a <> None.
Proof.
intros H mem a Hr. unfold aview, mbyte. destruct (mrestrict H mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate|].
destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|] eqn:E; [cbn; discriminate | congruence].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* image B's record of the image facts a walk cannot compute over an abstract SEGS (lib/B/Prog/SegRecBase.v) *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the record's symbols are image B's (lib/B/YF0m.v): the stack guard's .got word and the memchr window's
   unownedness come from it (SegRecCells.seg_rec_cells, SegRecBase.seg_snl_unowned) *)
Hypothesis HSY : YF0m.SegBSyms B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B memchr_loA memchr_hiA (pa_sigma SS___interceptor_trampoline_memchr).

(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84e00 after addi sp,sp,-352) *)
Lemma k14_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 368 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
unfold x_s1, x_sp0, LT_FRAME in *. rewrite HLS in Hslo.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* a live block of a state is a harness block of that state: at or above 4096, 16-aligned, addressable *)
Lemma k14_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* lt_img reads only image bytes the runtime does not own (and ROM bytes, which every reader shows): a reader that
   keeps those bytes keeps lt_img (image A's s10_lt_img_kept, its facts from IMGF's fields); the stack guard's .got
   word, which the runtime owns, is re-read from AR at the new state (SegRecCells.seg_rec_cells) *)
Lemma k14_img_kept : forall cx ly S (W' : world SEGS) mem' md (rd : reader),
  AR SEGS B ly S W' mem' md ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
   rdW W' mem' a = rd a) ->
  lt_img B cx rd -> lt_img B cx (rdW W' mem').
Proof.
intros cx ly S W' mem' md rd HAR K (HRO & HIM & HGI).
assert (KI : forall q n, sa_img SEGS B q n -> forall a, q <= a < q + n -> rdW W' mem' a = rd a).
{ intros q n0 Hq a Ha. destruct (Hq a Ha) as (H1 & H2 & H3). exact (K a H1 H2 H3). }
assert (KW : forall q n a, sa_img SEGS B q n -> q <= a -> a + 8 <= q + n -> rdword (rdW W' mem') a = rdword rd a).
{ intros q n0 a Hq H1 H2. apply rdword_ext. intros k Hk. apply (KI q n0 Hq). lia. }
assert (KL : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s (Ha & ((Hz & Hn0) & _) & Hp & Hr & Hi). split; [exact Ha|]. split; [split; [split|]|].
  - intros i Hix. rewrite length_app in Hix. cbn [length] in Hix.
    rewrite (KI _ _ Hi); [exact (Hz i ltac:(rewrite length_app; cbn [length]; lia))|]. lia.
  - exact Hn0.
  - exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr).
  - split; [exact Hp|]. split; [exact Hr | exact Hi]. }
split; [|split].
- (* arodata_okP: every byte it reads is an image byte the runtime does not own *)
  intros a Hro Ho He. rewrite <- (HRO a Hro Ho He). apply K; [|exact Ho | exact He].
  destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
  exact (cif_relro_img _ _ IMGF a Hr).
- destruct HIM as (Hm40 & Hm40i & HLF & HLR & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr)
    & (Hg1 & Hg2) & HLP & HLT & HLI & HD1 & HD2 & HD3).
  split; [|split; [exact Hm40i|]].
  { intros k Hk. rewrite (KI _ _ Hm40i); [exact (Hm40 k Hk) | lia]. }
  split; [intros s Hs; destruct (HLF s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split; [intros s Hs; destruct (HLR s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split.
  { split; [exact Hcp|]. split; [exact Hci|]. intros i Hi. destruct (Hcr i Hi) as (tp & Htp & Hl).
    exists tp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hci); [exact Htp | |];
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *; lia. }
  split; [exact HCa|].
  split.
  { split; [exact Hwp|]. split; [exact Hwi|]. intros i Hi. destruct (Hwr i Hi) as (wp & Hwp' & Hl).
    exists wp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hwi); [exact Hwp' | lia | lia]. }
  split.
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi k Hk. rewrite (KI _ _ Hri); [exact (Hrr i Hi k Hk) | lia]. }
  split; [exact (proj1 (proj2 (SegRecCells.seg_rec_cells SEGS B LAWS HSY IMGF ly S W' mem' md HAR)))|].
  split; [exact HLP|]. split; [exact HLT|]. split; [exact HLI|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- intros i Hi. rewrite (KI _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HIM))))))))))))).
  + exact (HGI i Hi).
  + unfold LONGL_W, LONGL_N. lia.
Qed.

(* a chain for a call's chain_pre: the stack from S1 to the layout's top is mapped (the entry's astack_pres carried by
   the journal; longl, the footprint, is below the stack), and s0 = SP0 is at least S1 + 352 (image A's lk_chain) *)
Lemma k14_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof.
intros cx ly S W regs mem md k o HB HF Hra.
pose proof (k14_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (Esp : spZ regs = x_s1 cx)
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
apply chain_pre_any; [exact Hra| |].
- rewrite Esp. apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia.
- rewrite Esp, Es0. lia.
Qed.

(* the facts of a point after one allocator call of the harness at sp = S1: the journal from the entry goes on with
   one event, the kept registers and every byte the facts read are the same, the new block joins the harness's
   (newest first), the budget pays one event (image A's lk_after_alloc with image B's frame slots 200 and 184) *)
Lemma k14_after_alloc : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res nb slo,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, nb)] ->
  acall_kept SEGS B ly S W memT W2 mem2 slo (x_s1 cx) (fun a => res <= a < res + req_size nb) ->
  mo_le MT S S2 (mo_malloc MT nb) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) /\
  lt_hblk B ly2 S2 (rdW W2 mem2) res nb /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) /\
  (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < m -> rdW W2 mem2 (b + i) = rdW W memT (b + i)).
Proof.
intros cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb slo HB HC Hrem Hnb HJ2 HP Hfr2 Hbl HKc MLE.
pose proof (k14_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HKc as (K1 & K2 & K3 & K4 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HinF2 : In (LT_FCLS, x_fpos cx) (frames S2)) by (rewrite Hfr2; exact HinF).
assert (HinB2 : In (res, nb) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (k14_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (EF2 : frame_addr ly2 LT_FCLS (x_fpos cx) = x_fr cx) by exact (k14_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W memT md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) as (_ & Hr4096 & Hrceil & Hrapp & _ & _ & _).
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
  apply K1; [split; [lia | exact (proj2 Ha)] |]. intros [_ Hc]. lia. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - cbv beta. intros Hr.
    pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res nb LT_FCLS (x_fpos cx) HAR2 HinB2 HinF2) as Hsep.
    rewrite EF2, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W memT (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - cbv beta. intros Hr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hrapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hr.
    pose proof (req_size_pos nb ltac:(lia)) as [Hq1 _]. lia. }
(* the bytes of the blocks live before the call *)
assert (KB : forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < m -> rdW W2 mem2 (b + i) = rdW W memT (b + i)).
{ intros b m i Hin Hi. pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
  apply (K2 b m i Hin ltac:(lia)). cbv beta. intros Hr.
  destruct (in_split _ _ Hin) as (l1 & l2 & El).
  assert (E2 : ablocks B ly2 S2 = l1 ++ (b, m) :: l2 ++ (res, nb) :: []) by (rewrite Hbl, El, <- app_assoc; reflexivity).
  pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (b, m) (res, nb) l1 l2 [] HAR2 E2) as Hsep.
  unfold zdisjoint, block_rng in Hsep. cbn [fst snd] in Hsep.
  pose proof (req_size_pos nb ltac:(lia)) as [Hq1 _]. lia. }
split; [|split; [exact (k14_hblk ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) | split; [exact KS | exact KB]]].
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (k14_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (k14_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (k14_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (k14_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (k14_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (k14_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (k14_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (k14_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (k14_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (k14_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (k14_word_kept (rdW W memT)); [|exact H200]; intros x Hx; apply KS; lia|].
  split.
  { intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)). }
  apply (k14_word_kept (rdW W memT)); [|exact H184]; intros x Hx; apply KS; lia.
- (* the image facts *)
  apply (k14_img_kept cx ly2 S2 W2 mem2 md2 (rdW W memT) HAR2 K3 HI).
- (* the blocks *)
  unfold lt_blocks in *. rewrite Hbl.
  eapply Permutation_trans; [apply Permutation_app_tail; exact HBL|].
  cbn [app]. apply Permutation_sym. apply Permutation_cons_append.
- (* the budget *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
  pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
  pose proof (mo_free_nonneg MT MTL) as M3.
  assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
  unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.

(* the facts of a point carried to a memory that agrees with it outside one window [wlo, whi) above the allocator's
   ceiling and below S1 + 184 (a run's slot stores below 176(s1), a runtime entry's scratch window below S1), at the
   same journal count, with sp, gp, tp, s0 and s1 kept (image A's lk_core_run, for any such window) *)
Lemma k14_core_keep : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' wlo whi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> rdW W mem' a = rdW W mem a) ->
  alloc_ceiling <= wlo -> wlo <= whi -> whi <= x_s1 cx + 184 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' wlo whi HB HC HJ' HK Hlo Hlh Hhi P2 P3 P4 P8 P9.
pose proof (k14_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (k14_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < wlo \/ whi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (k14_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (k14_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (k14_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (k14_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (k14_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left; unfold LT_FLAGW in *; lia|].
  split; [apply (k14_word_kept (rdW W mem)); [|exact H200]; intros x Hx; apply KA; right; lia|].
  split.
  { intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
    unfold x_sh, shadow_addr, SHADOW_OFF. lia. }
  apply (k14_word_kept (rdW W mem)); [|exact H184]; intros x Hx; apply KA; right; lia.
- apply (k14_img_kept cx ly S W mem' md' (rdW W mem) (proj1 HJ')); [|exact HI].
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* the premises an allocator call of the harness asks, from lt_core at the call (image A's lk_call_pre) *)
Lemma k14_call_pre : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> k14_bsum O + nb <= LIVE_LTOI ->
  spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx) /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\ x_s1 cx - x_sp0 cx <= 0 /\
  - LTOI_FRAME_MAX <= x_s1 cx - x_sp0 cx /\
  getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\ st_nev S < EV_MAX /\
  blocks_bytes S + nb <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT nb).
Proof.
intros cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum.
pose proof (k14_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _ & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
assert (HRU : LT_U MT <= rem * LT_U MT) by nia.
split; [unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; lia|].
split.
{ replace (x_s1 cx - x_sp0 cx) with (x_s1 cx + (- (x_sp0 cx / 16)) * 16)
    by (pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)); lia).
  rewrite Z_mod_plus_full. pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)).
  replace (x_s1 cx) with ((x_s1 cx / 32 * 2) * 16) by lia. apply Z_mod_mult. }
split; [lia|]. split; [unfold LTOI_FRAME_MAX in *; lia|].
split; [rewrite R3; exact Hgp0|]. split; [rewrite R4; exact Htp0|].
split; [unfold EV_LTOI in *; lia|].
split.
{ rewrite (k14_blocks_bytes B ly S), (k14_bsum_perm _ _ HBL), k14_bsum_app.
  unfold x_bl0. rewrite <- (k14_blocks_bytes B (x_ly cx) (x_S cx)). unfold LIVE_LTOI in *. lia. }
apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_malloc MT nb) MTL Hmo B4 M0). lia.
Qed.

(* ---- one call of the malloc wrapper (the trampoline the listing's PCall names) from a point where lt_core holds
   (image A's lt_malloc_at) ---- *)
Lemma k14_malloc_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> k14_bsum O + nb <= LIVE_LTOI ->
  getr regsT 10 = w64 nb -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) ->
     lt_hblk B ly2 S2 (rdW W2 mem2) res nb ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     (forall b m i, In (b, m) (ablocks B ly S) -> 0 <= i < m -> rdW W2 mem2 (b + i) = rdW W memT (b + i)) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_malloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O nb raw Q HB HC Hrem Hnb Hsum H10 H1 Hraw Hra4 HK.
destruct (k14_call_pre cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum)
  as (Hsp & Ho16 & Ho0 & Hom & Hgp & Htp & Hnev & Hlv & MOK).
pose proof HC as (HF & _).
pose proof (proj1 HF) as HJ.
pose proof ltoi_stk_room as HSR.
destruct (k14_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ exact (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k nb
    (x_s1 cx - x_sp0 cx) raw ch HJ H10 ltac:(unfold MALLOC_MAX; lia) Hlv Hsp Ho16 Ho0 ltac:(lia) Hgp Htp H1 Hraw
    Hnev Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr & _ & Hbl & HKp & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (k14_after_alloc cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb _
  HB HC Hrem Hnb HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HH2 & HK2 & HKB).
exact (HK ly2 S2 W2 regs2 mem2 md2 res HC2 HH2 HPr Hres HK2 HKB).
Qed.

(* ---- the payload's bytes along the journal from the entry while its block is live: the block is off the image
   (SegPaLib.v blk_off_imgP), the footprint ltoi_PG longlA outside it (image A's s25_payload_kept) ---- *)
Lemma k14_payload_kept : forall cx ly S (W : world SEGS) mem md own k,
  lt_base B MT cx ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) own ly S W mem md k ->
  (0 < x_n cx -> In (x_p cx, x_n cx) (ablocks B ly S)) ->
  forall i, 0 <= i < x_n cx -> rdW W mem (x_p cx + i) = rdW (x_W cx) (x_mem cx) (x_p cx + i).
Proof.
intros cx ly S W mem md own k HB HJ Hin i Hi.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & Hpn & _).
destruct Hpn as [[Hn0 _] | [Hn Hin0]]; [lia|].
pose proof (Hin ltac:(lia)) as Hin1.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hrq].
apply (F2 (x_p cx) (x_n cx) i Hin0 Hin1); [lia|].
pose proof (blk_off_imgP B _ _ _ _ _ _ _ (proj1 HPRE) Hin0) as Hoff.
intros (r & Hr & Hlo & Hhi). unfold ltoi_PG, longlA, A_LONGL, LONGL_N in Hr. unfold off_img in Hoff.
cbn [In] in Hr. destruct Hr as [<- | []]; cbn [fst snd] in Hlo, Hhi; lia.
Qed.
(* the payload is live at every point of the harness (lt_blocks keeps the entry's blocks) *)
Lemma k14_payload_live : forall cx ly S O, lt_base B MT cx -> lt_blocks B cx ly S O ->
  0 < x_n cx -> In (x_p cx, x_n cx) (ablocks B ly S).
Proof.
intros cx ly S O HB HBL Hn. pose proof HB as (_ & _ & _ & _ & _ & _ & Hpn & _).
destruct Hpn as [[Hn0 _] | [_ Hin0]]; [lia|].
apply (Permutation_in _ (Permutation_sym HBL)). apply in_or_app. right. exact Hin0.
Qed.
(* byte j of the payload, at a point where lt_core holds *)
Lemma k14_payload_rd : forall cx ly S (W : world SEGS) regs mem md k acc rem o O,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  forall j, (j < length (x_pl cx))%nat ->
  rdW W mem (x_p cx + Z.of_nat j) = Some (bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0))).
Proof.
intros cx ly S W regs mem md k acc rem o O HB HC j Hj.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HLEN & HGA & _).
pose proof HC as ((HJ & _) & _ & HBL & _).
rewrite (k14_payload_kept cx ly S W mem md [(LT_FCLS, x_fpos cx)] k HB HJ
  (k14_payload_live cx ly S O HB HBL) (Z.of_nat j) ltac:(lia)).
unfold aview. rewrite (garr8_mbyte SEGS _ _ _ j HGA ltac:(rewrite length_map; exact Hj)).
assert (Enth : nth j (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 = bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0))).
{ rewrite (nth_indep (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 (bv_unsigned (Z_to_bv 8 0)))
    by (rewrite length_map; exact Hj).
  exact (map_nth (fun b : byte => bv_unsigned b) (x_pl cx) (Z_to_bv 8 0) j). }
cbn [option_map]. rewrite Enth, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* the cursor's bytes at x_cur, at a point where lt_core holds *)
Lemma k14_cur_rd : forall cx ly S (W : world SEGS) regs mem md k acc rem o O f,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  forall i, (i < length (seg_spec.seg_cur (x_pl cx) f))%nat ->
  rdW W mem (x_cur cx f + Z.of_nat i) = Some (nth i (seg_spec.seg_cur (x_pl cx) f) 0).
Proof.
intros cx ly S W regs mem md k acc rem o O f HB HC i Hi.
destruct (k14_cur_nth (x_pl cx) f i Hi) as [HL E]. rewrite E.
unfold x_cur, seg_spec.seg_cur_at.
replace (x_p cx + Z.of_nat (length (x_pl cx)) - Z.of_nat (length (seg_spec.seg_cur (x_pl cx) f)) + Z.of_nat i)
  with (x_p cx + Z.of_nat (length (x_pl cx) - length (seg_spec.seg_cur (x_pl cx) f) + i)) by lia.
apply (k14_payload_rd cx ly S W regs mem md k acc rem o O HB HC). lia.
Qed.

(* ---- the memchr wrapper (interceptor row 20, MemchrDef.amemchr_realizesM) in the art_post form PaArt's call
   step takes, with the ESTACK scratch window (fuzz_command's _s41.v aw_snl_art_loc) ---- *)
Lemma k14_mch_art : forall ly S (W : world SEGS) regs mem md x n,
  ecall_pre_stk SEGS B ESTACK ly S W regs mem md ->
  getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 < x ->
  aread_ok SEGS ESTACK W regs mem x n ->
  ConstsViewDef.consts_view SEGS memchr_loA memchr_hiA W mem ->
  SRr SEGS W (cfg_at SEGS (pa_sigma SS___interceptor_trampoline_memchr) regs mem md)
    (art_post SEGS B ESTACK ly S W regs mem md (fun _ => False)
       (fun regs' _ => exists kk, first_byte SEGS W mem x n 0 kk /\
          getr regs' 10 = (if kk <? n then w64 (x + kk) else w64 0))).
Proof.
intros ly S W regs mem md x n (HPRE & Hlo & Hscr) H10 H11 H12 Hx (R0 & R1 & R2 & R3 & R4 & R5 & R6) HCV.
eapply SRr_mono.
{ apply (AMEMCHR fx ly S W regs mem md x 0 n HPRE H10 H11 H12 ltac:(lia) R2 Hx R1).
  - intros a Ha. destruct (R3 a Ha) as [Hv Hs]. split; [exact Hv|]. unfold ascratch_stk in Hs. exact Hs.
  - exact R4.
  - exact R5.
  - exact R6.
  - exact HCV. }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR & HP & Hs & HQ & Hfr & Hpres).
split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HAR|]. split; [exact HP|]. split; [exact Hs|]. split; [exact HQ|].
split; [intros a Ha Hw _; exact (Hfr a Ha Hw)|]. split; [exact Hpres|].
intros a Ha. apply Hpres. apply Hscr. exact Ha.
Qed.

(* memchr's window of read-only constants reads as the image, from lt_img's arodata_okP *)
Lemma k14_consts : forall cx (W : world SEGS) mem, lt_img B cx (rdW W mem) ->
  ConstsViewDef.consts_view SEGS memchr_loA memchr_hiA W mem.
Proof.
intros cx W mem (HRO & _) a Ha. destruct (seg_snl_unowned B HSY a Ha) as (Ho & He).
apply (HRO a); [|exact Ho | exact He].
left. destruct (cif_snl_rom _ _ IMGF a Ha) as (sg & Hsg & Hw & Hr). exists sg. exact (conj Hsg (conj Hw Hr)).
Qed.

(* ---- one call of the memchr wrapper from a point where lt_core holds, over bytes of the payload's block: lt_core
   is kept at the same count, the callee-saved registers too, and every byte outside the scratch window [S1 -
   ESTACK, S1); a0 answers memchr ---- *)
Lemma k14_memchr_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O x n raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 n ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  0 < x_n cx -> x_p cx <= x -> x + n <= x_p cx + x_n cx -> 0 <= n ->
  (forall regs2 mem2 md2 kk,
     lt_core B MT cx ly S W regs2 mem2 md2 k acc rem o O ->
     aregs_preserved regsT regs2 ->
     first_byte SEGS W memT x n 0 kk -> getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W memT a) ->
     SRr SEGS W (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_memchr)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O x n raw Q HB HC H10 H11 H12 H1 Hraw Hn Hx1 Hx2 Hn0 HK.
pose proof (k14_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & HI & HBL & _).
pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof HB as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof (proj1 HJ) as HAR.
pose proof asan_consts as (C1 & _).
pose proof ltoi_stk_room as HSR.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
assert (HinP : In (x_p cx, x_n cx) (ablocks B ly S)) by exact (k14_payload_live cx ly S O HB HBL Hn).
assert (Hsp : spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx))
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; lia).
assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ replace (x_s1 cx - x_sp0 cx) with (x_s1 cx + (- (x_sp0 cx / 16)) * 16)
    by (pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)); lia).
  rewrite Z_mod_plus_full. pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)).
  replace (x_s1 cx) with ((x_s1 cx / 32 * 2) * 16) by lia. apply Z_mod_mult. }
destruct (al_blocks _ _ LAWS ly S W memT md _ _ HAR HinP) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
assert (HRD : aread_ok SEGS ESTACK W regsT memT x n).
{ apply (aread_ok_of_block SEGS B LAWS ESTACK ly S W regsT memT md (x_p cx) (x_n cx));
    [exact HAR | exact HinP | lia | lia | lia |].
  rewrite Hsp, Hes. unfold LTOI_FRAME_MAX in *. lia. }
assert (HraT : YK0s.ret_ok (getr regsT 1)) by (rewrite H1; exact Hraw).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False)
    (pa_sigma SS___interceptor_trampoline_memchr)
    W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k (x_s1 cx - x_sp0 cx) raw
    (fun regs' _ => exists kk, first_byte SEGS W memT x n 0 kk /\
       getr regs' 10 = (if kk <? n then w64 (x + kk) else w64 0))
    HJ Hsp Ho16 ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite Hes, HLS; unfold LTOI_FRAME_MAX in *; lia) H1
    (fun a (H : False) => False_ind _ H)).
  apply (k14_mch_art ly S W regsT memT md x n).
  - exact (ecall_pre_stk_at SEGS B ESTACK STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx)
      (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT md k regsT (x_s1 cx - x_sp0 cx) HJ Hsp Ho16
      ltac:(lia) ltac:(lia) ltac:(rewrite Hes, HLS; unfold LTOI_FRAME_MAX in *; lia)
      HraT ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0)).
  - exact H10.
  - exact H11.
  - exact H12.
  - lia.
  - exact HRD.
  - exact (k14_consts cx W memT HI). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (kk & Hfb & HQ) & HK2).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - ESTACK <= a < x_s1 cx) -> rdW W mem2 a = rdW W memT a).
{ intros a Ha Hw. apply HK2; [exact Ha | | tauto]. replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by ring.
  exact Hw. }
apply (HK regs2 mem2 md2 kk); [| exact HP2 | exact Hfb | exact HQ | exact KM].
apply (k14_core_keep cx ly S W regsT memT md k acc rem o O regs2 mem2 md2 (x_s1 cx - ESTACK) (x_s1 cx) HB HC HJ2 KM).
- rewrite Hes. lia.
- rewrite Hes. lia.
- lia.
- exact (k14_pres_reg _ _ 2%bv 2 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (k14_pres_reg _ _ 3%bv 3 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (k14_pres_reg _ _ 4%bv 4 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (k14_pres_reg _ _ 8%bv 8 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
- exact (k14_pres_reg _ _ 9%bv 9 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
Qed.

End e.
End f.
End d.
