(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif0cgif.v (a working branch 30a1993588f, c5 + memnorm; file sha256 7fa49e0df3d0) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* The cgif_file instance of the Deallocate interface's image class ImgBaseDG.DImg: the constant cells' zone and the
   instance object's range (AGif0cgif.CZONE / inst_ok), the depot's and the internal allocator's zones and the internal
   allocator's initialized cells (DGgi.DZONE / IZONE / IAL_POST), the application zones (YF0x.zone3) and the entry
   pcs of StackDepotPut, QuarantineCache::Enqueue, Quarantine::Drain, QuarantineCallback::Recycle and CacheDealloc
   (YFl0.A_StackDepotPut, YFew.A_Enqueue, YFeu.A_Drain / A_RChunk / A_CDealloc).  The image-free files DGif0, DMspec
   and DMiface take the class as [Context {IM : AImg} {DI : DImg}]; a cgif_file consumer does
   [Require Import AGif2cgif DGif0cgif] and instance search fills IM with AImg_cgif and DI with DImg_cgif, so
   [dg_dzone] unfolds to DGgi.DZONE by delta.  This is the ONE file of the cgif instance of DImg: a field added to DImg
   gets its cgif value here.  Consumers relocated to another binary declare their own instance in place of this
   file.  The checks at the end confirm that each ImgBaseDG copy is convertible with its original. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFew AFeu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif0reply DGbase DGgi DGgm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseDG DMspec.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[export] Instance DImg_reply : DImg := {|
  dg_czone := AGif0reply.CZONE; dg_inst_ok := AGif0reply.inst_ok;
  dg_dzone := DGgi.DZONE; dg_izone := DGgi.IZONE; dg_ial_post := DGgi.IAL_POST;
  dg_zone3 := AF0x.zone3;
  dg_depot := A_StackDepotPut; dg_enqueue := A_Enqueue;
  dg_drain := A_Drain; dg_rchunk := A_RChunk; dg_cdealloc := A_CDealloc
|}.
End a.
(* Also a canonical structure, as AGif2cgif.AImg_cgif: a tactic that elaborates its term without instance search must
   solve [dg_dzone ?DI = DGgi.DZONE] by unification alone. *)
Canonical Structure DImg_reply.

(* The released names of the drain contract (DMspec.drain_spec_cf / drain_spec_cf_free), for a user that has not
   renamed yet. *)
Notation tfib_drain_spec_cf := drain_spec_cf.
Notation tfib_drain_spec_cf_free := drain_spec_cf_free.

(* Each copy in ImgBaseDG is its original, up to conversion. *)
Check (eq_refl : @DGbaseC.DFSTACK = @DGbase.DFSTACK).
Check (eq_refl : @YFewC.QSTACK = @AFew.QSTACK).
Check (eq_refl : @YFl0C.DEP_STK = @AFl0.DEP_STK).
Check (eq_refl : @YFl0C.depot_after = @AFl0.depot_after).
Check (eq_refl : @YFeuC.DSTACK = @AFeu.DSTACK).
Check (eq_refl : @YFeuC.transfer_g = @AFeu.transfer_g).
Check (eq_refl : @YFeuC.recycle_body = @AFeu.recycle_body).
Check (eq_refl : @YFeuC.drain_body = @AFeu.drain_body).
Check (eq_refl : @YFeuC.plist_cells = @AFeu.plist_cells).
Check (eq_refl : @YFeuC.puser = @AFeu.puser).
Check (eq_refl : @DGgiC.SPv = @DGgi.SPv).
Check (eq_refl : @DGgiC.N8v = @DGgi.N8v).
Check (eq_refl : @DGgiC.CNT8v = @DGgi.CNT8v).
Check (eq_refl : @DGgiC.Bv = @DGgi.Bv).
Check (eq_refl : @DGgiC.BBv = @DGgi.BBv).
Check (eq_refl : @DGgiC.BCv = @DGgi.BCv).
Check (eq_refl : @DGgiC.SLOTv = @DGgi.SLOTv).
Check (eq_refl : @DGgiC.QSv = @DGgi.QSv).
Check (eq_refl : @DGgiC.QFv = @DGgi.QFv).
Check (eq_refl : @DGgiC.QBv = @DGgi.QBv).
Check (eq_refl : @DGgiC.PSTATIC = @DGgi.PSTATIC).
Check (eq_refl : @DGgiC.PBDISJ = @DGgi.PBDISJ).
Check (eq_refl : @DGgiC.WINT = @DGgi.WINT).
Check (eq_refl : @DGgiC.WINB = @DGgi.WINB).
Check (eq_refl : @DGgmC.WINT = @DGgm.WINT).
Check (eq_refl : @DGgmC.WINB = @DGgm.WINB).
