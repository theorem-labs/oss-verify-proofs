(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the symbolic executor's branch conditions of the four
   strip loops, as Z facts. The loops load a text byte into a register (`lbu`, the executor's SExt false 8 of the
   byte's atom) and test it with `bltu s3, x` (s3 = 32) and `srl x', s9, x; andi x', x', 1; beqz x'` (s9 = the blank
   mask 0x100002200, m_file_m.v MF_BLANK): hda_U_zext8 and hda_U_mask give the values U takes (by computation over
   the bytes), so a branch of the loop is a fact about SegModel.blank of the byte. The HDRA segment lane of the G2 walk owner's
   G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI09 YN3v YK04 YA0i YA0n YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegABase m_file_m m_file_s_hdra_t.
Import ListNotations.
Open Scope Z_scope.

Lemma hda_byte_nat : forall b, 0 <= b < 256 -> exists k, b = Z.of_nat k /\ (k < 256)%nat.
Proof. intros b Hb. exists (Z.to_nat b). split; lia. Qed.

(* the byte the executor loads: U of the zero-extended low byte of an atom holding the byte b *)
Lemma hda_U_zext8 : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 -> U E (SExt false 8 (SOff n 0)) = b.
Proof.
  intros E n b Hn Hb. unfold U. cbn [sv_denot]. rewrite Hn.
  destruct (hda_byte_nat b Hb) as (k & -> & Hk). clear Hb Hn.
  do 256 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
(* the mask test of a byte b <= 32: bit b of 0x100002200 is the blank test *)
Lemma hda_U_mask : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b <= 32 ->
  U E (SAlu ALU_AND (SAlu ALU_SRL (SLit 0x100002200) (SExt false 8 (SOff n 0))) (SLit 1)) =
  if blank b then 1 else 0.
Proof.
  intros E n b Hn Hb. unfold U. cbn [sv_denot]. rewrite Hn.
  assert (Hk : exists k, b = Z.of_nat k /\ (k <= 32)%nat) by (exists (Z.to_nat b); split; lia).
  destruct Hk as (k & -> & Hk). clear Hb Hn.
  do 33 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
(* the loops' two exits on a byte: above 32, or at most 32 and its mask bit 0, is a non-blank byte; at most 32
   and its mask bit 1 is a blank one *)
Lemma hda_nonblank_gt : forall b, 32 < b -> blank b = false.
Proof. exact hda_blank_gt32. Qed.
Lemma hda_blank_of_mask : forall b, 0 <= b <= 32 -> (if blank b then 1 else 0) <> 0 -> blank b = true.
Proof. intros b _ H. destruct (blank b); [reflexivity | exfalso; exact (H eq_refl)]. Qed.
Lemma hda_nonblank_of_mask : forall b, 0 <= b <= 32 -> (if blank b then 1 else 0) = 0 -> blank b = false.
Proof. intros b _ H. destruct (blank b); [discriminate H | reflexivity]. Qed.

(* ============================== the text through a reader ============================== *)
(* byte x of the text left rest at p (its NUL at x = |rest|) *)
Lemma hda_txt_byte : forall rd p rest x, sa_str rd p rest -> (x <= length rest)%nat ->
  rd (p + Z.of_nat x) = Some (nth x rest 0).
Proof.
  intros rd p rest x ((HZ & _) & _) Hx.
  rewrite (HZ x ltac:(rewrite length_app; cbn [length]; lia)).
  destruct (Nat.eq_dec x (length rest)) as [->|Hne].
  - rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
  - rewrite app_nth1 by lia. reflexivity.
Qed.
(* a sub-range of an addressable range is addressable *)
Lemma hda_hull_sub : forall (rd : reader) q n q' n', shadow_hull_vis rd q n -> 0 < n' -> q <= q' -> q' + n' <= q + n ->
  shadow_hull_vis rd q' n'.
Proof.
  intros rd q n q' n' H Hn' H1 H2 s Hs. apply H. unfold shadow_addr in *.
  assert (A1 : q / 8 <= q' / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : (q' + n' - 1) / 8 <= (q + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (B1 : (SHADOW_OFF + q / 8) / 8 * 8 <= (SHADOW_OFF + q' / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
  assert (B2 : (SHADOW_OFF + (q' + n' - 1) / 8) / 8 * 8 <= (SHADOW_OFF + (q + n - 1) / 8) / 8 * 8).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. }
  lia.
Qed.
Lemma hda_addr_sub : forall rd q n q' n', sa_addr rd q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' ->
  sa_addr rd q' n'.
Proof.
  intros rd q n q' n' (H1 & H2 & H3 & H4 & H5) Hq Hn Hn0.
  split; [lia|]. split; [lia|]. split.
  - unfold amem_range in *. destruct H3 as [H3|[H3a H3b]]; [left; lia | right; split; lia].
  - split; [exact (range_addressable_sub rd SHADOW_OFF q n q' n' H4 Hq Hn)|].
    intros Hn'. apply (hda_hull_sub rd q n q' n'); [apply H5; lia | lia | lia | lia].
Qed.

Section fb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* memchr(s, c, j - i) over the stripped line sl = slice i j (mf_line rest) at s = p + i: the wrapper's answer kk
   (MemchrDef's first_byte) is the model's memchr of sl *)
Lemma hda_memchr_of_fb : forall segs (W : world segs) mem p rest i j c kk,
  sa_str (aview segs (w_H W) mem) p rest -> (i <= j <= length (mf_line rest))%nat ->
  first_byte segs W mem (p + Z.of_nat i) (Z.of_nat (j - i)) c kk ->
  exists k : nat, kk = Z.of_nat k /\ (k <= length (slice i j (mf_line rest)))%nat /\
  memchr (slice i j (mf_line rest)) c =
    (if (k <? length (slice i j (mf_line rest)))%nat then Some k else None).
Proof.
  intros segs W mem p rest i j c kk HS Hij (Hk & Hne & Heq).
  pose proof (hda_line_le rest) as HL.
  assert (Lsl : length (slice i j (mf_line rest)) = (j - i)%nat) by (apply hda_slice_length; lia).
  assert (Hb : forall x, (x < j - i)%nat ->
    aview segs (w_H W) mem (p + Z.of_nat i + Z.of_nat x) = Some (nth x (slice i j (mf_line rest)) 0)).
  { intros x Hx. rewrite hda_sl_nth by lia. replace (p + Z.of_nat i + Z.of_nat x) with (p + Z.of_nat (i + x)) by lia.
    apply hda_txt_byte; [exact HS | lia]. }
  exists (Z.to_nat kk). split; [lia|]. split; [rewrite Lsl; lia|].
  apply hda_memchr_of_first.
  - rewrite Lsl. lia.
  - intros x Hx Ex. destruct (Hne (Z.of_nat x) ltac:(lia)) as (b & Hb1 & Hb2).
    rewrite (Hb x ltac:(lia)) in Hb1. injection Hb1 as <-. exact (Hb2 Ex).
  - intros Hx. rewrite Lsl in Hx. pose proof (Heq ltac:(lia)) as H1.
    replace kk with (Z.of_nat (Z.to_nat kk)) in H1 by lia.
    rewrite (Hb (Z.to_nat kk) Hx) in H1. injection H1 as H1. exact H1.
Qed.
End fb.
