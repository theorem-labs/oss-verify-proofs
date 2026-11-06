(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 456 of its 574 lines of code are new or changed and 409 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/U/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 476 of its 543 lines of code are new or changed and 507 lines of the source are left out. *)
(* Segment L01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (UBSan, ELF afc060e3cc9c): [0x139e4, 0x13aa8],
   K139e4 f -> K13aac f (U/Prog/LLVMFuzzerTestOneInput_c.v's S_L01, at the cut record CPseg of
   U/Prog/Seg/SegWalkMainA.v). The plain file's walk (Prog/Seg/L01.v) on the UBSan code
   (51 instructions, 11 conditional branches): s3 the cursor
   and s1 the count left (P_K139e4); s9 = s3 + 1, + 2, + 3 as the label byte and the u16 are read (s8, a0, a1), and
   the three UBSan pointer-overflow checks of fuzz_u8 (`bgeu 1, s9` to the `unimp` at 0x14264)
   are not taken because the cursor is nonzero and the input ends below 2^63; s6 = min(len, s1) (`bltu`); the
   take's two checks (0x13a64 `add s3,s6,s9`, `bltu s3,s9`: no wrap; 0x13a6c-0x13a78 `snez`/`seqz`/`xor`/`beqz`:
   s9 and s3 both nonzero) are not taken; for s6 <> 0, memchr(s9, 0, s6) at 0x13a8c (ra 0x13a90) through
   U/Prog/memchr_c.memchr_contract; s10 = (a0 ? a0 - s9 : s6); a0 = s10 + 1 and `jal malloc` at 0x13aa8 (ra 0x13aac),
   run by Tac_b1.b1_malloc_call from hb = hb_cm bc bm. Its continuation closes Inv_K13aac f with P_K13aac (s10 = n,
   s6 = n', s9 = the take's address, s3 = that address + n', s1 = the count before the take, s8 = lb).
   The pure lemmas (the cursor is a suffix of the input, the f-th record is read at it, the four shapes of the
   cursor's bytes) are the plain file's, restated here over the UBSan build's StrFun.
   Part of the proof of LLVMFuzzerTestOneInput (one segment of its walk); no released proof of fuzz_segconf's
   LLVMFuzzerTestOneInput exists. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_cuts memchr_c SegEnd.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b8 SegWalkMainA.
Import ListNotations.
Open Scope Z_scope.

(* ---- The payload at the cursor (Spec/SegModel.v, Prog/seg_spec.v) ---- *)
(* s is a suffix of l. *)
Definition l01_sfx (s l : list Z) : Prop := exists pre, l = pre ++ s.

Lemma l01_sfx_refl : forall l, l01_sfx l l.
Proof. intros l. exists []. reflexivity. Qed.

Lemma l01_sfx_trans : forall a b c, l01_sfx a b -> l01_sfx b c -> l01_sfx a c.
Proof. intros a b c (p1 & ->) (p2 & ->). exists (p2 ++ p1). rewrite app_assoc. reflexivity. Qed.

Lemma l01_sfx_u8 : forall l, l01_sfx (snd (fuzz_u8 l)) l.
Proof. intros [|b l]; cbn [fuzz_u8 snd]; [exists []; reflexivity | exists [b]; reflexivity]. Qed.

Lemma l01_sfx_u16 : forall l, l01_sfx (snd (fuzz_u16 l)) l.
Proof.
  intros l. unfold fuzz_u16.
  pose proof (l01_sfx_u8 l) as H1. revert H1. destruct (fuzz_u8 l) as [lo i1]. cbn [snd]. intros H1.
  pose proof (l01_sfx_u8 i1) as H2. revert H2. destruct (fuzz_u8 i1) as [hi i2]. cbn [snd]. intros H2.
  exact (l01_sfx_trans _ _ _ H2 H1).
Qed.

Lemma l01_sfx_take : forall l n, l01_sfx (snd (fuzz_take l n)) l.
Proof.
  intros l n. cbv beta zeta delta [fuzz_take]. cbn [snd].
  exists (firstn (Nat.min (Z.to_nat n) (length l)) l). symmetry. apply firstn_skipn.
Qed.

Lemma l01_sfx_skip : forall k l, l01_sfx (seg_skip k l) l.
Proof.
  induction k as [|k IH]; intros l; cbn [seg_skip]; [apply l01_sfx_refl|].
  pose proof (l01_sfx_u8 l) as H1. revert H1. destruct (fuzz_u8 l) as [lb i1]. cbn [snd]. intros H1.
  pose proof (l01_sfx_u16 i1) as H2. revert H2. destruct (fuzz_u16 i1) as [len i2]. cbn [snd]. intros H2.
  pose proof (l01_sfx_take i2 len) as H3. revert H3. destruct (fuzz_take i2 len) as [q i3]. cbn [snd]. intros H3.
  exact (l01_sfx_trans _ _ _ (IH i3) (l01_sfx_trans _ _ _ H3 (l01_sfx_trans _ _ _ H2 H1))).
Qed.

(* The cursor after k records is a suffix of the input. *)
Lemma l01_cur_sfx : forall inp k, l01_sfx (seg_cur inp k) (seg_in inp).
Proof.
  intros inp k. unfold seg_cur, seg_hdr.
  eapply l01_sfx_trans; [apply l01_sfx_skip|].
  eapply l01_sfx_trans; [apply l01_sfx_u8|].
  eapply l01_sfx_trans; [apply l01_sfx_u8|].
  apply l01_sfx_u8.
Qed.

Lemma l01_skipn_zs : forall k (l : list byte), skipn k (zs l) = zs (skipn k l).
Proof. unfold zs. induction k as [|k IH]; intros [|b l]; cbn [skipn map]; try reflexivity. apply IH. Qed.

Lemma l01_firstn_zs : forall k (l : list byte), firstn k (zs l) = zs (firstn k l).
Proof. unfold zs. induction k as [|k IH]; intros [|b l]; cbn [firstn map]; try reflexivity. f_equal. apply IH. Qed.

Lemma l01_zs_len : forall l : list byte, length (zs l) = length l.
Proof. intros l. unfold zs. apply length_map. Qed.

Lemma l01_skipn_pre : forall (pre s : list Z), skipn (length pre) (pre ++ s) = s.
Proof. induction pre as [|x pre IH]; intros s; [reflexivity|]. cbn [length app skipn]. apply IH. Qed.

(* A suffix s of the input's bytes is the zs of the input's last length s bytes. *)
Lemma l01_sfx_bytes : forall (inp : list byte) s, l01_sfx s (zs inp) ->
  (length s <= length inp)%nat /\ zs (skipn (length inp - length s) inp) = s.
Proof.
  intros inp s (pre & E).
  assert (HL : length inp = (length pre + length s)%nat).
  { rewrite <- (l01_zs_len inp), E, length_app. reflexivity. }
  split; [lia|].
  replace (length inp - length s)%nat with (length pre) by lia.
  rewrite <- l01_skipn_zs, E. apply l01_skipn_pre.
Qed.

(* The file records: dec_files k l has k entries, the f-th read at the cursor after f records. *)
Lemma l01_dec_len : forall k l, length (dec_files k l) = k.
Proof.
  induction k as [|k IH]; intros l; cbn [dec_files]; [reflexivity|].
  destruct (fuzz_u8 l) as [lb i1]. destruct (fuzz_u16 i1) as [len i2]. destruct (fuzz_take i2 len) as [q i3].
  cbn [length]. rewrite IH. reflexivity.
Qed.

Lemma l01_dec_nth : forall f k l, (f < k)%nat ->
  nth f (dec_files k l) (File 0 []) =
  File (fst (fuzz_u8 (seg_skip f l)))
       (fuzz_str (fst (fuzz_take (snd (fuzz_u16 (snd (fuzz_u8 (seg_skip f l)))))
                                 (fst (fuzz_u16 (snd (fuzz_u8 (seg_skip f l)))))))).
Proof.
  induction f as [|f IH]; intros k l Hf; (destruct k as [|k]; [lia|]); cbn [dec_files seg_skip].
  - destruct (fuzz_u8 l) as [lb i1]; cbn [fst snd].
    destruct (fuzz_u16 i1) as [len i2]; cbn [fst snd].
    destruct (fuzz_take i2 len) as [q i3]; cbn [fst snd nth]. reflexivity.
  - destruct (fuzz_u8 l) as [lb i1]; cbn [fst snd].
    destruct (fuzz_u16 i1) as [len i2]; cbn [fst snd].
    destruct (fuzz_take i2 len) as [q i3]; cbn [fst snd nth]. apply IH. lia.
Qed.

Lemma l01_files : forall inp, seg_files inp =
  dec_files (Z.to_nat (1 + fst (fuzz_u8 (snd (fuzz_u8 (snd (fuzz_u8 (seg_in inp)))))) mod 4)) (seg_hdr inp).
Proof.
  intros inp. unfold seg_files, seg_pay, decode, seg_hdr.
  destruct (fuzz_u8 (seg_in inp)) as [b0 i1]; cbn [fst snd].
  destruct (fuzz_u8 i1) as [fl i2]; cbn [fst snd].
  destruct (fuzz_u8 i2) as [b2 i3]; cbn [fst snd p_files]. reflexivity.
Qed.

(* Turn f's reads at the cursor seg_cur inp f: lb, the u16 length, the bytes left after them, the bytes fuzz_take
   takes and their count, and the text's length (the taken bytes cut at their first NUL). *)
Definition l01_lb (l : list Z) : Z := fst (fuzz_u8 l).
Definition l01_tl (l : list Z) : list Z := snd (fuzz_u16 (snd (fuzz_u8 l))).
Definition l01_len (l : list Z) : Z := fst (fuzz_u16 (snd (fuzz_u8 l))).
Definition l01_take (l : list Z) : list Z := fst (fuzz_take (l01_tl l) (l01_len l)).
Definition l01_np (l : list Z) : Z := Z.of_nat (length (l01_take l)).
Definition l01_n (l : list Z) : Z := Z.of_nat (length (fuzz_str (l01_take l))).

Lemma l01_file : forall inp f, Z.of_nat f < seg_nfiles inp ->
  seg_file inp f = File (l01_lb (seg_cur inp f)) (fuzz_str (l01_take (seg_cur inp f))).
Proof.
  intros inp f Hf. unfold seg_nfiles in Hf. unfold seg_file, l01_lb, l01_take, l01_tl, l01_len, seg_cur.
  rewrite l01_files in Hf |- *. apply l01_dec_nth. rewrite l01_dec_len in Hf. lia.
Qed.

Lemma l01_lb_eq : forall inp f, Z.of_nat f < seg_nfiles inp -> seg_lb inp f = l01_lb (seg_cur inp f).
Proof. intros inp f Hf. unfold seg_lb. rewrite (l01_file inp f Hf). reflexivity. Qed.

Lemma l01_txt_eq : forall inp f, Z.of_nat f < seg_nfiles inp -> seg_txt_n inp f = l01_n (seg_cur inp f).
Proof. intros inp f Hf. unfold seg_txt_n, seg_txt. rewrite (l01_file inp f Hf). reflexivity. Qed.

Lemma l01_np_eq : forall inp f, seg_turn_np inp f = l01_np (seg_cur inp f).
Proof. reflexivity. Qed.

Lemma l01_tl_eq : forall inp f, seg_turn_tail inp f = l01_tl (seg_cur inp f).
Proof. reflexivity. Qed.

(* The text is at most 65535 bytes. *)
Lemma l01_n_le : forall l, 0 <= l01_n l <= l01_np l /\ l01_np l <= 65535.
Proof.
  intros l. unfold l01_n, l01_np, fuzz_str.
  pose proof (cut_nul_len (l01_take l)) as H1.
  assert (H2 : (length (l01_take l) <= Z.to_nat (l01_len l))%nat).
  { unfold l01_take. cbv beta zeta delta [fuzz_take]. cbn [fst]. rewrite length_firstn. lia. }
  assert (H3 : 0 <= l01_len l <= 65535).
  { unfold l01_len, fuzz_u16. destruct (fuzz_u8 (snd (fuzz_u8 l))) as [lo i1].
    destruct (fuzz_u8 i1) as [hi i2]. cbn [fst]. apply land65535. }
  lia.
Qed.

(* ---- The four shapes of the cursor's bytes ---- *)
Lemma l01_take_nil : forall l, l01_tl l = [] -> l01_take l = [].
Proof. intros l H. unfold l01_take. rewrite H. cbv beta zeta delta [fuzz_take]. cbn [fst]. apply firstn_nil. Qed.

Lemma l01_shape0 : l01_lb (zs []) = 0 /\ l01_tl (zs []) = [] /\ l01_np (zs []) = 0 /\ l01_n (zs []) = 0.
Proof.
  assert (E : l01_take (zs []) = []) by (apply l01_take_nil; reflexivity).
  unfold l01_np, l01_n. rewrite E. repeat split; reflexivity.
Qed.

Lemma l01_shape1 : forall b0 : byte,
  l01_lb (zs [b0]) = bv_unsigned b0 /\ l01_tl (zs [b0]) = [] /\ l01_np (zs [b0]) = 0 /\ l01_n (zs [b0]) = 0.
Proof.
  intros b0. assert (E : l01_take (zs [b0]) = []) by (apply l01_take_nil; reflexivity).
  unfold l01_np, l01_n. rewrite E. repeat split; reflexivity.
Qed.

Lemma l01_shape2 : forall b0 b1 : byte,
  l01_lb (zs [b0; b1]) = bv_unsigned b0 /\ l01_tl (zs [b0; b1]) = [] /\ l01_np (zs [b0; b1]) = 0 /\
  l01_n (zs [b0; b1]) = 0.
Proof.
  intros b0 b1. assert (E : l01_take (zs [b0; b1]) = []) by (apply l01_take_nil; reflexivity).
  unfold l01_np, l01_n. rewrite E. repeat split; reflexivity.
Qed.

(* lo | hi << 8 for two bytes: lo + 256 hi (checked on the 65536 pairs). *)
Lemma l01_lor_all : forallb (fun lo => forallb (fun hi => Z.lor lo (Z.shiftl hi 8) =? lo + hi * 256)
    (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma l01_lor : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> Z.lor lo (Z.shiftl hi 8) = lo + hi * 256.
Proof.
  intros lo hi Hlo Hhi. pose proof l01_lor_all as H.
  rewrite forallb_forall in H.
  assert (Hl : In lo (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat lo). split; [lia|]. apply in_seq. lia. }
  specialize (H lo Hl). rewrite forallb_forall in H.
  assert (Hh : In hi (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat hi). split; [lia|]. apply in_seq. lia. }
  apply Z.eqb_eq. exact (H hi Hh).
Qed.

Lemma l01_byte : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R. Qed.

Lemma l01_len3 : forall (b0 b1 b2 : byte) r,
  l01_len (zs (b0 :: b1 :: b2 :: r)) = bv_unsigned b1 + bv_unsigned b2 * 256.
Proof.
  intros b0 b1 b2 r. unfold l01_len, fuzz_u16. cbn [zs map fuzz_u8 fst snd].
  rewrite (l01_lor _ _ (l01_byte b1) (l01_byte b2)).
  pose proof (l01_byte b1). pose proof (l01_byte b2).
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma l01_shape3 : forall (b0 b1 b2 : byte) r,
  l01_lb (zs (b0 :: b1 :: b2 :: r)) = bv_unsigned b0 /\ l01_tl (zs (b0 :: b1 :: b2 :: r)) = zs r /\
  l01_take (zs (b0 :: b1 :: b2 :: r)) =
    zs (firstn (Nat.min (Z.to_nat (bv_unsigned b1 + bv_unsigned b2 * 256)) (length r)) r).
Proof.
  intros b0 b1 b2 r. split; [reflexivity|]. split; [reflexivity|].
  unfold l01_take. rewrite l01_len3. change (l01_tl (zs (b0 :: b1 :: b2 :: r))) with (zs r).
  cbv beta zeta delta [fuzz_take]. cbn [fst]. rewrite l01_zs_len, l01_firstn_zs. reflexivity.
Qed.

(* The text's length is the index of the first NUL of the taken bytes, or their count. *)
Lemma l01_cut_len : forall bs : list byte,
  Z.of_nat (length (cut_nul (zs bs))) =
  match find_byte 0 bs with Some i => Z.of_nat i | None => Z.of_nat (length bs) end.
Proof.
  unfold zs. induction bs as [|b bs IH]; cbn [map cut_nul find_byte length]; [reflexivity|].
  destruct (bv_unsigned b =? 0); [reflexivity|]. cbn [length].
  revert IH. destruct (find_byte 0 bs) as [i|]; intros IH; lia.
Qed.

(* memchr's premise: it reads only the n bytes of the buffer. *)
Lemma l01_mok : forall A c n buf, 0 <= n <= Z.of_nat (length buf) -> memchr_ok A c n buf.
Proof.
  intros A c n buf Hn. unfold memchr_ok. destruct (find_byte c (firstn (Z.to_nat n) buf)); [left|]; lia.
Qed.

Lemma l01_n3 : forall (b0 b1 b2 : byte) r k,
  k = Nat.min (Z.to_nat (bv_unsigned b1 + bv_unsigned b2 * 256)) (length r) ->
  l01_np (zs (b0 :: b1 :: b2 :: r)) = Z.of_nat k /\
  l01_n (zs (b0 :: b1 :: b2 :: r)) =
    match find_byte 0 (firstn k r) with Some i => Z.of_nat i | None => Z.of_nat k end.
Proof.
  intros b0 b1 b2 r k Hk. destruct (l01_shape3 b0 b1 b2 r) as (_ & _ & E). rewrite <- Hk in E.
  unfold l01_np, l01_n, fuzz_str. rewrite E, l01_zs_len, length_firstn, l01_cut_len.
  split; [lia|]. destruct (find_byte 0 (firstn k r)); [reflexivity|]. rewrite length_firstn. lia.
Qed.

(* ---- Bytes and words ---- *)
Lemma l01_rng : forall x : word, 0 <= bv_unsigned x < 2 ^ 64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. exact R. Qed.

Lemma l01_weq : forall (x : word) e, bv_unsigned x mod 2 ^ 64 = e mod 2 ^ 64 -> x = Z_to_bv 64 e.
Proof. intros x e H. rewrite <- (Z_to_bv_lit_self x). apply Z_to_bv_eqm. exact H. Qed.

Lemma l01_rd0 : forall m (a : word) b l, bytes_at rsegs m (bv_unsigned a) (b :: l) ->
  ov_read_bytes rsegs m a 1 = Some [b].
Proof.
  intros m a b l H.
  assert (E : a = wa (bv_unsigned a + Z.of_nat 0)).
  { unfold wa. rewrite Z.add_0_r. symmetry. apply Z_to_bv_lit_self. }
  rewrite E. rewrite (bytes_at_ov_read rsegs m (bv_unsigned a) (b :: l) 0 1 H) by (cbn; lia). reflexivity.
Qed.

Lemma l01_rd1 : forall m a b0 b1 l, bytes_at rsegs m a (b0 :: b1 :: l) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + 1)) 1 = Some [b1].
Proof. intros m a b0 b1 l H. exact (bytes_at_ov_read rsegs m a _ 1 1 H ltac:(cbn; lia)). Qed.

Lemma l01_rd2 : forall m a b0 b1 b2 l, bytes_at rsegs m a (b0 :: b1 :: b2 :: l) ->
  ov_read_bytes rsegs m (Z_to_bv 64 (a + 2)) 1 = Some [b2].
Proof. intros m a b0 b1 b2 l H. exact (bytes_at_ov_read rsegs m a _ 2 1 H ltac:(cbn; lia)). Qed.

Lemma l01_ba3 : forall m a b0 b1 b2 l, bytes_at rsegs m a (b0 :: b1 :: b2 :: l) -> bytes_at rsegs m (a + 3) l.
Proof.
  intros m a b0 b1 b2 l H. change (b0 :: b1 :: b2 :: l) with ([b0; b1; b2] ++ l) in H.
  apply bytes_at_app in H as [_ H]. exact H.
Qed.

(* 0x13948 `or s6,a1,a0` after `slli a1,a1,8`: lo | hi << 8 = lo + 256 hi. *)
Lemma l01_or_val : forall b1 b2 : byte,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (zxb b2)) 8))) (bv_unsigned (zxb b1))) =
  Z_to_bv 64 (bv_unsigned b1 + bv_unsigned b2 * 256).
Proof.
  intros b1 b2. f_equal. unfold zxb. pose proof (l01_byte b1). pose proof (l01_byte b2).
  rewrite (unsigned_lit (bv_unsigned b2)) by lia. rewrite (unsigned_lit (bv_unsigned b1)) by lia.
  rewrite unsigned_lit by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm. apply l01_lor; assumption.
Qed.

(* memchr's answer on the taken bytes. *)
Lemma l01_mres : forall A c n buf A' k, A = A' -> c = 0 -> n = Z.of_nat k ->
  memchr_res A c n buf = match find_byte 0 (firstn k buf) with Some i => A' + Z.of_nat i | None => 0 end.
Proof. intros A c n buf A' k -> -> ->. unfold memchr_res. rewrite Nat2Z.id. reflexivity. Qed.

(* A rw_cells on the normalized memory holds on the memory itself (they agree on every byte read). *)
Lemma l01_rw_unnorm : forall m A cs, ro_agree rsegs m -> rw_cells rsegs (normalize rsegs m) A cs ->
  rw_cells rsegs m A cs.
Proof.
  intros m A cs Hro ((Hwf & Hb) & Hw). pose proof (mem_rel_normalize rsegs m Hro) as HR.
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m _ _ _ HR) Hb)] | exact (wr_at_rel rsegs m _ _ _ HR Hw)].
Qed.

(* ---- The run: K139e4 to malloc's entry with ra = 0x13aac ---- *)
Definition l01_post (sp gp tp s0 s2 s4 s5 s7 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (a : Z) (cb : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s8' s9' s10' t3' t4' t5' t6' : word)
         (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x13aac) sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7'
                  s2 s3' s4 s5 s6' s7 s8' s9' s10' s11 t3' t4' t5' t6')
             F (Z_to_bv 64 0x17518) fc None m' (seg_rom rsegs) /\
    a0' = Z_to_bv 64 (l01_n (zs cb) + 1) /\
    s1' = Z_to_bv 64 (Z.of_nat (length (l01_tl (zs cb)))) /\
    s3' = Z_to_bv 64 (a + Z.of_nat (length cb) - Z.of_nat (length (l01_tl (zs cb))) + l01_np (zs cb)) /\
    s6' = Z_to_bv 64 (l01_np (zs cb)) /\
    s8' = Z_to_bv 64 (l01_lb (zs cb)) /\
    s9' = Z_to_bv 64 (a + Z.of_nat (length cb) - Z.of_nat (length (l01_tl (zs cb)))) /\
    s10' = Z_to_bv 64 (l01_n (zs cb)) /\
    Frame.munch [] m m' /\ Frame.wmono rsegs m m' /\ mem_inv rsegs m'.

(* The truth values of the take's null check (0x13a6c `snez a0,s9`, 0x13a70 `seqz a1,s3`, 0x13a74 `xor`) when the
   facts decide each comparison. *)
Ltac l01_b2z H :=
  repeat match type of H with
  | context [Z.b2z (?a <? ?b)] =>
      first [ rewrite (proj2 (Z.ltb_lt a b)) in H by lia | rewrite (proj2 (Z.ltb_ge a b)) in H by lia ]
  end; cbn [Z.b2z] in H; rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in H.

(* A branch: rewrite a comparison of two literals, then keep the side the facts allow (every UBSan trap branch,
   to the `unimp` at 0x14264, is refuted here). *)
Ltac l01_if :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      try (rewrite b8_eqb_lit by lia); try (rewrite b8_ltu_lit by lia);
      let H := fresh "EC" in if_cases H; zify_cond H;
      repeat (rewrite MState.unsigned_lit in H by lia);
      l01_b2z H;
      try (exfalso; lia);
      try (exfalso; lazymatch type of H with context [bv_unsigned ?x] => pose proof (l01_rng x); lia end)
  | _ => idtac
  end.

(* Step to the next stop: malloc's entry, memchr's entry, or (l01_to) the `bltu` / the take's `add`. *)
Ltac l01_go :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x17518) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1edcc) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14264) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => l01_if
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
  end.

Ltac l01_to :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x17518) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1edcc) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x14264) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x13a5c) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x13a64) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => l01_if
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
  end.

Ltac l01_eq := first [ reflexivity | apply l01_weq; rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia ].

Ltac l01_fin :=
  apply evt_done; unfold l01_post;
  do 22 eexists; split; [reflexivity|];
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [assumption|split; [assumption|assumption]]]]]]]]].

Lemma l01_evt : memchr_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cb : list byte),
    bv_unsigned s1 = Z.of_nat (length cb) -> 0 < bv_unsigned s3 ->
    bv_unsigned s3 + Z.of_nat (length cb) < 2 ^ 63 ->
    bytes_at rsegs m (bv_unsigned s3) cb -> mem_inv rsegs m ->
    evt rsegs (l01_post sp gp tp s0 s2 s4 s5 s7 s11 F fc m (bv_unsigned s3) cb)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x139e4) fc None m (seg_rom rsegs)).
Proof.
  intros MCHR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m cb Hs1 Hs3 Hhi HB HMI.
  unfold memchr_contract in MCHR.
  pose proof (munch_refl [] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (l01_rng s3) as Rs3.
  destruct cb as [|b0 [|b1 [|b2 r]]]; cbn [length] in Hs1, Hhi.
  - (* no byte left: s8 = 0, len = 0, s6 = 0 *)
    destruct l01_shape0 as (Q_lb & Q_tl & Q_np & Q_n).
    l01_go. l01_fin.
    all: rewrite ?Q_lb, ?Q_tl, ?Q_np, ?Q_n; cbn [length]; l01_eq.
  - (* one byte: the label byte, len = 0 *)
    destruct (l01_shape1 b0) as (Q_lb & Q_tl & Q_np & Q_n).
    pose proof (l01_rd0 _ _ _ _ HB) as HR0.
    l01_go. l01_fin.
    all: rewrite ?Q_lb, ?Q_tl, ?Q_np, ?Q_n; cbn [length]; l01_eq.
  - (* two bytes: len = data[1], nothing left to take *)
    destruct (l01_shape2 b0 b1) as (Q_lb & Q_tl & Q_np & Q_n).
    pose proof (l01_rd0 _ _ _ _ HB) as HR0.
    pose proof (l01_rd1 _ _ _ _ _ HB) as HR1.
    l01_go. l01_fin.
    all: rewrite ?Q_lb, ?Q_tl, ?Q_np, ?Q_n; cbn [length]; l01_eq.
  - (* three or more bytes: len = lo + 256 hi, k = min(len, left) bytes taken *)
    pose proof (l01_rd0 _ _ _ _ HB) as HR0.
    pose proof (l01_rd1 _ _ _ _ _ HB) as HR1.
    pose proof (l01_rd2 _ _ _ _ _ _ HB) as HR2.
    pose proof (l01_ba3 _ _ _ _ _ _ HB) as HBr.
    pose proof (l01_byte b0) as Hb0. pose proof (l01_byte b1) as Hb1. pose proof (l01_byte b2) as Hb2.
    destruct (l01_shape3 b0 b1 b2 r) as (Q_lb & Q_tl & _).
    remember (Nat.min (Z.to_nat (bv_unsigned b1 + bv_unsigned b2 * 256)) (length r)) as k eqn:Hk.
    destruct (l01_n3 b0 b1 b2 r k Hk) as (Q_np & Q_n).
    l01_to. step.
    rewrite (l01_or_val b1 b2).
    replace (Z_to_bv 64 (bv_unsigned s1 + -3)) with (Z_to_bv 64 (Z.of_nat (length r))) by (f_equal; lia).
    l01_if.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x13a60) _ _ _ _) => step
         | _ => idtac
         end.
    all: first [ replace (Z_to_bv 64 (bv_unsigned b1 + bv_unsigned b2 * 256)) with (Z_to_bv 64 (Z.of_nat k))
                   by (f_equal; lia)
               | replace (Z_to_bv 64 (Z.of_nat (length r))) with (Z_to_bv 64 (Z.of_nat k)) by (f_equal; lia) ].
    all: l01_go.
    (* k = 0: no memchr *)
    all: try (l01_go; l01_fin;
              rewrite ?Q_lb, ?Q_tl, ?Q_np, ?Q_n, ?l01_zs_len; cbn [length];
              try (replace k with 0%nat by lia; cbn [firstn find_byte]); l01_eq).
    (* k <> 0: memchr(s3 + 3, 0, k) *)
    all: l01_go.
    all: lazymatch goal with
         | |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
             eapply evt_cut;
             [ eapply MCHR with (buf := r);
               [ rewrite unsigned_lit by lia; exact HBr
               | apply l01_mok; rewrite unsigned_lit by lia; lia
               | assumption ]
             | post_call segs mm ]
         end.
    all: lazymatch goal with
         | |- context [memchr_res ?A ?c ?n ?buf] =>
             rewrite (l01_mres A c n buf (bv_unsigned s3 + 3) k)
               by first [ rewrite unsigned_lit by lia; lia | reflexivity | vm_compute; reflexivity ]
         end.
    all: destruct (find_byte 0 (firstn k r)) as [i|] eqn:EF.
    all: try (destruct (find_byte_Some _ _ _ EF) as (Hi & _ & _); rewrite length_firstn in Hi).
    all: l01_go; l01_fin.
    all: rewrite ?Q_lb, ?Q_tl, ?Q_np, ?Q_n, ?l01_zs_len, ?EF; cbn [length]; l01_eq.
Qed.


(* The last bytes of a byte run. *)
Lemma l01_ba_skip : forall m a (bs : list byte) k, bytes_at rsegs m a bs -> (k <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia. exact H.
Qed.

(* ---- The segment ---- *)
Ltac l01_rp RP Hx r :=
  etransitivity; [exact (RP r ltac:(unfold callee_saved; lia))|]; rewrite (sl_getr_eqv _ _ _ Hx).

Section L01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts_ubsan B APIf LS SH SK ra empty.
Hypothesis MCHR : memchr_contract.

Lemma seg_L01 : S_L01 B APIf ra empty CPseg.
Proof using fx rc B APIf LS SH SK ra empty FF MCHR.
  unfold S_L01. intros f H1 g c (Hf4 & bc & bm & HC).
  eapply (b8_cut_open B APIf ra empty); [exact HC|].
  intros fx' L A regs mem md Hfrm HFR HP HPk.
  cbn [cp_K139e4 CPseg] in HPk. unfold P_K139e4 in HPk.
  destruct HPk as (Hfn & HLC & H8 & H19 & H9 & H20 & HRC & HMC).
  pose proof (sl_segs B APIf ra empty FF) as SEGS.
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & Hsp16 & HSKb & HS47 & HMI).
  pose proof HFR as (HGV & _ & _ & _ & _ & _ & _ & _ & HM & _).
  pose proof HGV as (Hn26 & Hpl & _).
  pose proof alloc_ceiling_lt as HAC.
  (* The cursor's bytes: the input block's last |seg_cur| bytes (none for the empty input). *)
  pose proof (l01_cur_sfx (g_in g) f) as HSFX.
  destruct (l01_sfx_bytes (g_in g) (seg_cur (g_in g) f) HSFX) as (Hcl & Hzs).
  remember (skipn (length (g_in g) - length (seg_cur (g_in g) f)) (g_in g)) as cb eqn:Ecb.
  assert (Hcbl : length cb = length (seg_cur (g_in g) f)) by (rewrite <- Hzs; symmetry; apply l01_zs_len).
  assert (HCB : bytes_at rsegs (normalize rsegs mem) (seg_cur_at (g_in g) (g_p g) f) cb /\
                0 < seg_cur_at (g_in g) (g_p g) f /\
                seg_cur_at (g_in g) (g_p g) f + Z.of_nat (length cb) < 2 ^ 63).
  { unfold seg_cur_at. destruct Hpl as [(Hn0 & Hpe) | (Hn0 & Hinb)].
    - assert (Ein : g_in g = []) by (apply length_zero_iff_nil; unfold g_n in Hn0; lia).
      assert (Ecur : length (seg_cur (g_in g) f) = 0%nat).
      { assert (E0 : length (g_in g) = 0%nat) by (rewrite Ein; reflexivity). lia. }
      pose proof (ff_empty B APIf ra empty FF) as Hemp.
      assert (Ecb0 : cb = []) by (destruct cb as [|? ?]; [reflexivity | cbn [length] in Hcbl; lia]).
      rewrite Ecb0, Ecur, Ein, Hpe. cbn [length].
      split; [apply sl_bytes_nil; lia|]. lia.
    - destruct (b1_in_all B APIf ra empty FF g _ L A regs mem md HFR HP Hn0) as (_ & Hp4096 & Hpac & HBY).
      unfold g_n in Hpac.
      pose proof (l01_ba_skip _ _ _ (length (g_in g) - length (seg_cur (g_in g) f)) HBY ltac:(lia)) as HB.
      rewrite <- Ecb in HB. rewrite Nat2Z.inj_sub in HB by exact Hcl. rewrite Z.add_sub_assoc in HB.
      split; [|split; [lia | rewrite Hcbl; lia]].
      exact (bytes_at_normalize rsegs mem _ _ HMI HB). }
  destruct HCB as (HCB & Hcur0 & Hcurh). clear Ecb.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  rewrite SEGS.
  eapply (sl_run regs (Z_to_bv 64 0x139e4) mem md _ _ Hh Hl HMI).
  - rewrite sl_mkR_of.
    assert (E19 : bv_unsigned (YK11.getr regs 19) = seg_cur_at (g_in g) (g_p g) f).
    { rewrite H19. apply MState.unsigned_lit. lia. }
    apply (l01_evt MCHR) with (cb := cb).
    + rewrite H9. unfold seg_cur_n. rewrite MState.unsigned_lit by (rewrite <- Hcbl in *; lia).
      rewrite Hcbl. reflexivity.
    + rewrite E19. exact Hcur0.
    + rewrite E19. exact Hcurh.
    + rewrite E19. exact HCB.
    + exact (mem_inv_normalize rsegs mem).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m0 & -> & _).
    do 3 eexists. reflexivity.
  - intros R pc' m0' HQ regs' m' Hx Hrel Hsame.
    destruct HQ as (t0' & t1' & t2' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & s3' & s6' & s8' & s9' &
                    s10' & t3' & t4' & t5' & t6' & m'' & HE & Ea0 & Es1 & Es3 & Es6 & Es8 & Es9 & Es10 & MU & WM &
                    MIv).
    injection HE; intros; subst.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    pose proof (munch_rel rsegs _ mem (normalize rsegs mem) m' _ HR0 Hrel Hsame MU) as MU'.
    pose proof (wmono_rel rsegs mem (normalize rsegs mem) m' _ HR0 Hrel Hsame WM) as WM'.
    pose proof (ro_agree_same rsegs mem m' HMI Hsame) as Hro'.
    assert (HFR' : FR B APIf ra empty g (hb_cm bc bm) L A regs' m' md).
    { apply (b1_fr_hb B APIf ra empty FF g (hb_cm bc bm) [] L A regs mem md regs' m' HFR HP).
      - intros x [].
      - intros a _ _ _ _. apply MU'. exact I.
      - exact WM'.
      - exact Hro'.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
      - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
    (* The turn's values at the cursor. *)
    assert (Etxt : l01_n (zs cb) = seg_txt_n (g_in g) f) by (rewrite Hzs; symmetry; exact (l01_txt_eq _ _ Hfn)).
    pose proof (l01_n_le (zs cb)) as Hnle.
    assert (E1 : YK11.getr regs' 1 = Z_to_bv 64 0x13aac) by (rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    assert (E10 : YK11.getr regs' 10 = Z_to_bv 64 (TXT_N (g_in g) f)).
    { rewrite (sl_getr_eqv _ _ _ Hx). transitivity (Z_to_bv 64 (l01_n (zs cb) + 1)); [reflexivity|].
      unfold TXT_N. rewrite Etxt. reflexivity. }
    rewrite <- SEGS.
    apply (b1_malloc_call B APIf ra empty FF g (hb_cm bc bm) L A regs' m' md regs' (TXT_N (g_in g) f));
      [exact HFR' | exact HP | cbn; lia | unfold hb_bytes, hb_cm, M_SIZE, C_SIZE; cbn; lia
      | reflexivity | reflexivity | reflexivity
      | rewrite E1; vm_compute; reflexivity | exact E10 | unfold TXT_N; rewrite <- Etxt; lia |].
    intros L' A' regs'' mem'' md' res HF2 HP2 RP H10' Hres0 Hres16 HKF HKB.
    rewrite E1. apply H1. exists bc, bm, res, (TXT_N (g_in g) f), fx', L', A', regs'', mem'', md'.
    split; [reflexivity|]. split; [exact Hfrm|]. split; [exact HF2|]. split; [exact HP2|].
    cbn [cp_K13aac CPseg]. unfold P_K13aac.
    (* Bytes of the cut: through the run (no write) and malloc (frame cells, the blocks of hb kept). *)
    assert (KC : forall off v, 0 <= off <= 200 -> celz mem (g_S g) off v -> celz mem'' (g_S g) off v).
    { intros off v Hoff Hc. unfold celz in *.
      apply (b1_ba_mbyte m'); [exact (b1_keep [] mem m'' m' _ _ HMI MU Hrel I Hc)|].
      intros i Hi. rewrite length_le8 in Hi. apply HKF. unfold fsp, SLOT_FRAME, SEG_FRAME. lia. }
    assert (KB : forall a k bs, In (a, k) (hb_cm bc bm) -> Z.of_nat (length bs) <= k ->
                 bytes_at rsegs mem a bs -> bytes_at rsegs mem'' a bs).
    { intros a k bs Hin Hk Hb. apply (b1_ba_mbyte m'); [exact (b1_keep [] mem m'' m' _ _ HMI MU Hrel I Hb)|].
      intros i Hi. apply (HKB a k i Hin). lia. }
    destruct HLC as ((Hr18 & Hr27 & Hc8 & Hc10 & Hc20 & Hc48 & Hc50 & Hbc16 & Hbm16 & Hbcn & Hbmn) &
                     Hr21 & Hc28 & Hc30 & Hc38 & Hc40).
    destruct (b1_hb B APIf ra empty FF g _ res (TXT_N (g_in g) f) L' A' regs'' mem'' md' HF2 HP2
                (or_introl eq_refl)) as (STt & Ht4096 & Htc).
    destruct (sl_rw_of_stk _ _ _ res (Z.to_nat (TXT_N (g_in g) f)) STt ltac:(lia)
                ltac:(unfold TXT_N in *; rewrite <- Etxt in *; lia)) as (junk & HRWt).
    destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF2) as (_ & _ & _ & _ & HMI2).
    unfold rgz.
    split; [exact Hfn|].
    split; [reflexivity|].
    split.
    { split; [split; [l01_rp RP Hx 18; exact Hr18|]|].
      - split; [l01_rp RP Hx 27; exact Hr27|].
        split; [apply KC; [lia | exact Hc8]|]. split; [apply KC; [lia | exact Hc10]|].
        split; [apply KC; [lia | exact Hc20]|]. split; [apply KC; [lia | exact Hc48]|].
        split; [apply KC; [lia | exact Hc50]|].
        repeat split; assumption.
      - split; [l01_rp RP Hx 21; exact Hr21|].
        split; [apply KC; [lia | exact Hc28]|]. split; [apply KC; [lia | exact Hc30]|].
        split; [apply KC; [lia | exact Hc38]|]. apply KC; [lia | exact Hc40]. }
    split; [exact H10'|].
    split; [exact Hres16|].
    split; [exact (b1_blk_noimg_segs B APIf ra empty FF g _ res _ L' A' regs'' mem'' md' HF2 HP2
                     (or_introl eq_refl))|].
    split; [exists junk; exact (l01_rw_unnorm mem'' res _ HMI2 HRWt)|].
    split; [l01_rp RP Hx 26; transitivity (Z_to_bv 64 (l01_n (zs cb))); [reflexivity|]; rewrite Etxt; reflexivity|].
    split; [l01_rp RP Hx 22; transitivity (Z_to_bv 64 (l01_np (zs cb))); [reflexivity|];
            rewrite Hzs, <- l01_np_eq; reflexivity|].
    split; [l01_rp RP Hx 25;
            transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr regs 19) + Z.of_nat (length cb) -
                                      Z.of_nat (length (l01_tl (zs cb))))); [reflexivity|];
            rewrite H19, MState.unsigned_lit by lia; rewrite Hzs, <- l01_tl_eq;
            unfold seg_turn_at, seg_cur_at; f_equal; lia|].
    split; [l01_rp RP Hx 19;
            transitivity (Z_to_bv 64 (bv_unsigned (YK11.getr regs 19) + Z.of_nat (length cb) -
                                      Z.of_nat (length (l01_tl (zs cb))) + l01_np (zs cb))); [reflexivity|];
            rewrite H19, MState.unsigned_lit by lia; rewrite Hzs, <- l01_tl_eq, <- l01_np_eq;
            unfold seg_turn_at, seg_cur_at; f_equal; lia|].
    split; [l01_rp RP Hx 9; transitivity (Z_to_bv 64 (Z.of_nat (length (l01_tl (zs cb))))); [reflexivity|];
            rewrite Hzs, <- l01_tl_eq; reflexivity|].
    split; [l01_rp RP Hx 24; transitivity (Z_to_bv 64 (l01_lb (zs cb))); [reflexivity|];
            rewrite Hzs, <- (l01_lb_eq _ _ Hfn); reflexivity|].
    split; [l01_rp RP Hx 8; exact H8|].
    split; [l01_rp RP Hx 20; exact H20|].
    split.
    { destruct HRC as (bs & Hb & Henc). exists bs. split; [|exact Henc].
      apply (KB bc C_SIZE bs); [right; left; reflexivity | destruct Henc as (Hlen & _); unfold C_SIZE;
        unfold SEG_C_SIZE in Hlen; lia | exact Hb]. }
    { destruct HMC as (bs & Hb & Henc). exists bs. split; [|exact Henc].
      apply (KB bm M_SIZE bs); [left; reflexivity | destruct Henc as (Hlen & _); unfold M_SIZE;
        unfold SEG_M_SIZE in Hlen; lia | exact Hb]. }
Qed.

End L01.

Theorem seg_L01_holds : seg_L01_stmt CPseg memchr_contract.
Proof.
  intros fx rc B APIf LS SH SK ra empty FF MC.
  exact (@seg_L01 fx rc B APIf LS SH SK ra empty FF MC).
Qed.
