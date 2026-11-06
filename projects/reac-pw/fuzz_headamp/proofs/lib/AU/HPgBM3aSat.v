(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): the satisfiability witness, at image B's real
   segments (lib/AU/Img0U.v rsegs) and real errno cell, of the one new Section hypothesis of image B's M03.head piece
   (lib/AU/HPgBM3aHead.v): ERRNO_RW, "the errno cell lies in no read-only segment". The parse
   (reac_headamp_prop_parse_result, 0x849ac) may write the errno cell (its contract's write set names it), and the
   cuts after it carry rom_view; the two meet only when the cell is outside every read-only segment. At the real
   instance the errno cell is 0x5d812c (image B's start-up symbol record: TFIB_ERRNO of lib/AU/YF0m.v, whose field
   ts_errno fixes as_errno), inside the last writable PT_LOAD of image B. Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
Import ListNotations.
Local Open Scope Z_scope.

(* image B's errno cell at the real instance *)
Definition HQU_B_ERRNO : Z := 0x5d812c.

(* no read-only segment of image B meets [0x5d812c, 0x5d8130) *)
Lemma hqu_errno_rw_segs : forallb (fun s : Segment => seg_writable s ||
  (HQU_B_ERRNO + 4 <=? Z.of_N (seg_base s)) || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? HQU_B_ERRNO)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* the cell lies in a writable segment of image B (so the witness is not empty: the four bytes are image bytes) *)
Lemma hqu_errno_in_rw : existsb (fun s : Segment => seg_writable s &&
  (Z.of_N (seg_base s) <=? HQU_B_ERRNO) && (HQU_B_ERRNO + 4 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ERRNO_RW at the real errno cell *)
Lemma hqu_errno_rw_B : forall a, HQU_B_ERRNO <= a < HQU_B_ERRNO + 4 -> ~ in_rom rsegs a.
Proof.
intros a Ha (sg & Hin & Hw & Hr).
pose proof hqu_errno_rw_segs as HB. rewrite forallb_forall in HB. specialize (HB sg Hin).
rewrite Hw in HB. cbn [orb] in HB. apply orb_prop in HB.
destruct HB as [H|H]; apply Z.leb_le in H; lia.
Qed.
(* the same for any symbol record whose errno field is the real one (YF0m's ts_errno : as_errno B = TFIB_ERRNO) *)
Lemma hqu_errno_rw_of : forall B : asyms, as_errno B = HQU_B_ERRNO ->
forall a, as_errno B <= a < as_errno B + 4 -> ~ in_rom rsegs a.
Proof. intros B HB a Ha. rewrite HB in Ha. exact (hqu_errno_rw_B a Ha). Qed.
End w.

Print Assumptions hqu_errno_rw_B.
Print Assumptions hqu_errno_rw_of.
