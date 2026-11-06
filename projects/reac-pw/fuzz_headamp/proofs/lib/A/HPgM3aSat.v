(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47): the satisfiability witness, at image A's real
   segments and real errno cell, of the one new Section hypothesis of the M03.head piece (lib/A/HPgM3aHead.v):
   ERRNO_RW, "the errno cell lies in no read-only segment". The parse (reac_headamp_prop_parse_result) may write
   the errno cell (its contract's write set names it), and the cut after it carries rom_view; the two meet only
   when the cell is outside every read-only segment. At the real instance the errno cell is 0x5d7cac (the start-up
   symbol record's errno address, the field as_errno of the instance the start-up files fix), inside the
   writable PT_LOAD [0x9e068, 0x5f9630) of the image. Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0.
Import ListNotations.
Local Open Scope Z_scope.

(* image A's errno cell at the real instance *)
Definition HQ_A_ERRNO : Z := 0x5d7cac.

(* no read-only segment of image A meets [0x5d7cac, 0x5d7cb0) *)
Lemma hq_errno_rw_segs : forallb (fun s : Segment => seg_writable s ||
  (HQ_A_ERRNO + 4 <=? Z.of_N (seg_base s)) || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? HQ_A_ERRNO)) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* ERRNO_RW at the real errno cell *)
Lemma hq_errno_rw_A : forall a, HQ_A_ERRNO <= a < HQ_A_ERRNO + 4 -> ~ in_rom rsegs a.
Proof.
intros a Ha (sg & Hin & Hw & Hr).
pose proof hq_errno_rw_segs as HB. rewrite forallb_forall in HB. specialize (HB sg Hin).
rewrite Hw in HB. cbn [orb] in HB. apply orb_prop in HB.
destruct HB as [H|H]; apply Z.leb_le in H; lia.
Qed.
(* the same for any symbol record whose errno field is the real one *)
Lemma hq_errno_rw_of : forall B : asyms, as_errno B = HQ_A_ERRNO ->
forall a, as_errno B <= a < as_errno B + 4 -> ~ in_rom rsegs a.
Proof. intros B HB a Ha. rewrite HB in Ha. exact (hq_errno_rw_A a Ha). Qed.
End w.

Print Assumptions hq_errno_rw_A.
Print Assumptions hq_errno_rw_of.
