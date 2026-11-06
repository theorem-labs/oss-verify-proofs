(* libreac/fuzz_boxreg, build asan-ubsan: the asyms instance of lib/B/Rt/StrncmpViewB.v `abfm_ro_owned_pinned`, for box_segs
   and TfibB. Rule 24: no function is proved here. It discharges StrncmpView's state-free premise from three facts
   about this image and this instance:
   (1) in_rom box_segs a -> a lies in one of box_ro_ranges (the 2 non-writable PT_LOAD ranges): ro_segs_ok, a
       vm_compute over the concrete loaded segments, shows every non-writable segment is inside a box_ro_range;
   (2) abfm_ro_img_word box_segs = AF0mCheck.img_word (the same little-endian recursion over box_segs);
   (3) Tfib_const_abs is a part of as_const TfibB ly (= Tfib_const = Tfib_const_sym ++ Tfib_const_abs ++
       Tfib_const_shadow), and as_owned_static TfibB = Tfib_owned_static.
   With them AF0mCheck.box_ro_gate (over box_ro_ranges, Tfib_owned_static, Tfib_const_abs, img_word) gives
   StrncmpView.abfm_ro_owned_pinned (over in_rom, as_owned_static, as_const, abfm_ro_img_word). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI04 YI00 YM05 YF0p.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B Require Import AF0l AF0m ACej AF0mCheck AD2l.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Rt Require Import StrncmpDefB StrncmpViewB.
Import ListNotations.
Local Open Scope Z_scope.

(* (2) StrncmpView's abfm_ro_img_word at box_segs is AF0mCheck's img_word: the same recursion. *)
Lemma ro_img_word_box : forall w a, abfm_ro_img_word box_segs a w = img_word a w.
Proof.
  induction w as [|w IH]; intro a; cbn [abfm_ro_img_word img_word]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* (1) The non-writable loaded segments are the two RO PT_LOADs rounded up to a page, so they run a little past
   box_ro_ranges (the exact p_filesz extent). A byte that is both owned (Tfib_owned_static) and in_rom is still
   inside box_ro_ranges: every owned range that meets a non-writable segment lies within a box_ro_range (the
   owned globals sit inside p_filesz, never in a segment's page padding). owned_ro_ok is that, by vm_compute. *)
Definition seg_ov (r : Z * Z) (sg : Segment) : bool :=
  andb (negb (seg_writable sg))
    (andb (Z.of_N (seg_base sg) <? fst r + snd r) (fst r <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))).
Definition owned_ro_ok : bool :=
  forallb (fun r => implb (existsb (seg_ov r) box_segs)
    (existsb (fun q => (fst q <=? fst r) && (fst r + snd r <=? fst q + snd q)) box_ro_ranges)) Tfib_owned_static.
Lemma owned_ro_ok_true : owned_ro_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma owned_in_rom_ro_ranges : forall a, in_rom box_segs a ->
  Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static ->
  Exists (fun r => fst r <= a < fst r + snd r) box_ro_ranges.
Proof.
  intros a (sg & Hin & Hnw & Hlo & Hhi) Ho.
  apply Exists_exists in Ho as (r & Hr & Hro).
  pose proof (proj1 (forallb_forall _ _) owned_ro_ok_true r Hr) as H. cbv beta in H.
  assert (Hov : existsb (seg_ov r) box_segs = true).
  { apply existsb_exists. exists sg. split; [exact Hin|].
    unfold seg_ov. rewrite Hnw. cbn [negb andb]. apply andb_true_intro. split; apply Z.ltb_lt; lia. }
  rewrite Hov in H. cbn [implb] in H.
  apply existsb_exists in H as (q & Hq & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply Exists_exists. exists q. split; [exact Hq|]. lia.
Qed.

(* The discharge. *)
Theorem box_ro_owned_pinned : abfm_ro_owned_pinned box_segs TfibB.
Proof.
  intros ly a Hrom Ho.
  (* owned_static TfibB = Tfib_owned_static; in_zr a r = fst r <= a < fst r + snd r. *)
  assert (Ho' : Exists (fun r => fst r <= a < fst r + snd r) Tfib_owned_static).
  { revert Ho. cbn [as_owned_static TfibB]. apply Exists_impl. intros r Hr. exact Hr. }
  pose proof (box_ro_gate_holds a (owned_in_rom_ro_ranges a Hrom Ho') Ho') as HG.
  apply Exists_exists in HG as (c & Hc & a' & v & Ha & Hv & Hrg & Hw).
  apply Exists_exists. exists c. split.
  - cbn [as_const TfibB]. unfold Tfib_const. apply in_app_iff. right. apply in_app_iff. left. exact Hc.
  - exists a', v. rewrite ro_img_word_box. split; [exact Ha | split; [exact Hv | split; [exact Hrg | exact Hw]]].
Qed.
