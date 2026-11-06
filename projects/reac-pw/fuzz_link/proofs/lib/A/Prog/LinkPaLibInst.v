(* reac-pw/fuzz_link, image A: the record `PALib` of lib/A/Prog/LinkPaLib.v at link's asyms instance PcapB
   (lib/A/AD2l.v). Every walk of one of link's own functions takes `TL : PALib B`; this discharges it at B := PcapB.

   `PcapB_palib` holds at any image instance PI of link's listing whose value table is link's (`LinkVals`,
   lib/A/Prog/LinkWalk.v) and whose segments are the image's (`pa_segs = tfibsegs`, lib/A/AB1v.v). At link's
   instance (LinkImgInst.v PI_link) both premises are pi_link_vals / pi_link_segs. Its fields:
   - the shadow base's .got slot 0xa19d0 and cell 0xaa438, the side-stack switch's .got slot 0xa1a28 and cell
     0xaa440: AD2l.v's PcapB fields, equal to link_obj 1 / 64 / 0 / 65 of lib/A/Prog/LinkAddr.v;
   - api_env: errno (AF0m.v TFIB_ERRNO = 0x631b6c) below kLowMemEnd and inside one loaded segment (by
     computation over the segments), and the two allocator return addresses pc_malloc_ra0 = 0x5436c,
     pc_free_ra0 = 0x5420c (AF0l.v Tfib_code) as one-frame rows of the trace universe (ACej.v Tfib_universe, the
     fixed part of PcapB's universe ACejUniv.Tfib_univ);
   - the free / malloc wrappers' 4-byte jumps 0x540c8 / 0x540cc (LinkAddr.v link_sigma) are Tfib_code's
     pc_wrap_free / pc_wrap_malloc, and both return addresses lie below link_text 0x821cc.
   Its closure is the walk kit's plus the start-up files AD2l.v needs (AF0l, AF0m, AF0x, ACej, ACejTfib,
   ACejUniv); no allocator walk file.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal LinkSyms LinkList LinkAddr
LinkPa LinkPaLib LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0l AF0m AD2l.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require ACej ACejUniv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable lsym} {PL : PAListing L} {PI : PAImg L}.

(* errno's four bytes lie in one loaded segment of the image *)
Lemma tfib_errno_img : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> in_img tfibsegs a.
Proof.
  assert (H : existsb (fun sg => (Z.of_N (seg_base sg) <=? TFIB_ERRNO) &&
                                 (TFIB_ERRNO + 4 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool tfibsegs = true)
    by (vm_compute; reflexivity).
  apply existsb_exists in H as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  intros a Ha. exists sg. split; [exact Hin | lia].
Qed.

Lemma PcapB_palib : LinkVals -> pa_segs = tfibsegs -> PALib PcapB.
Proof.
  intros LV HS.
  assert (O0 : pa_val (A_OBJ 0) = 0xa1a28) by (rewrite (lv_obj LV 0) by (unfold link_nobj; lia); reflexivity).
  assert (O1 : pa_val (A_OBJ 1) = 0xa19d0) by (rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity).
  assert (O64 : pa_val (A_OBJ 64) = 0xaa438) by (rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity).
  assert (O65 : pa_val (A_OBJ 65) = 0xaa440) by (rewrite (lv_obj LV 65) by (unfold link_nobj; lia); reflexivity).
  assert (T : pa_val A_TEXT = 0x821cc) by (rewrite (lv_text LV); reflexivity).
  constructor.
  - rewrite O1. reflexivity.
  - rewrite O64. reflexivity.
  - rewrite O0. reflexivity.
  - rewrite O65. reflexivity.
  - rewrite O1, O64. lia.
  - rewrite HS. split; [|split].
    + change (as_errno PcapB) with TFIB_ERRNO. unfold TFIB_ERRNO, kLowMemEnd. lia.
    + change (as_errno PcapB) with TFIB_ERRNO. exact tfib_errno_img.
    + change (pc_malloc_ra0 (as_code PcapB)) with 0x5436c. change (pc_free_ra0 (as_code PcapB)) with 0x5420c.
      change (u_fix (as_universe PcapB)) with (u_fix ACejUniv.Tfib_univ). rewrite ACejUniv.Tfib_univ_fix.
      split; apply ACej.memZL_In; vm_compute; reflexivity.
  - rewrite (lv_sigma LV). reflexivity.
  - rewrite (lv_sigma LV). reflexivity.
  - rewrite T. change (pc_free_ra0 (as_code PcapB)) with 0x5420c. change (pc_malloc_ra0 (as_code PcapB)) with 0x5436c.
    lia.
Qed.
End i.

About PcapB_palib.
Print Assumptions PcapB_palib.
