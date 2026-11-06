(* fuzz_preset, image B' (asan-ubsan, pin d663f82d7f488d30, #102): the PAListing instance of h-verbs-1's listing of
   record lib/B/Listing_prog.v (blob 8bcc2c9e7809, cold/h-verbs-1-listing-pins102 d42e123915ae), for the B' walks while
   lib/B/PAImg_prog.v (blob 4392ab2c09ba) fails at :160 (B_prog_range waits for h-mani-a2's IMG_TOP_B = 0x601000):
   PL_prog_B is defined there at :177-181, after the failing lemma, so no walk can use it. The body below is
   PAImg_prog.v :177-181 with names suffixed B102 and B102_tpi pre-evaluated (below). It reads the listing only (no image address, no segment), so it
   is the same instance PL_prog_B will be once PAImg_prog.v builds; a walk over {PA : PAImg B_prog_listing} then
   instantiates PA := PI_prog_B. Owner: TxPutB102 (h-rw-pre-7's #102 lanes); shared with the fuzz_pick B' lane.
   rule 24: proves no function (kind: listing instance). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP0m YP09 YP02 YP0l YP0b YP0a YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YG00 YG0f YG0n YG0d YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog.
Import ListNotations.
Open Scope Z_scope.

(* PRE-EVALUATED (h-cmd-b1's measurement: an unevaluated ptree_of_list re-runs over the 7,776-slot listing on every
   vm_compute touching pl_tpi; ten lookups took 918 s / 146 GB, then OOM); pl_tpi_eq is then a kernel-checked
   vm_compute equation, as pl_tw_eq *)
Definition B102_tpi : ptree asym := Eval vm_compute in (ptree_of_list B_prog_listing).
Lemma B102_tpi_eq : ptree_of_list B_prog_listing = B102_tpi.
Proof. vm_compute. reflexivity. Qed.
Definition B102_tw : ctable := Eval vm_compute in (tw_of 0 B_prog_listing).
#[global] Instance PL_B102 : PAListing B_prog_listing :=
{| pl_tpi := B102_tpi; pl_tpi_eq := B102_tpi_eq; pl_tw := B102_tw; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.
