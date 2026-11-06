(* The tables of frame_alloc_9 (side stack for frames, class 9) on reac-pw/fuzz_link's asan image (pin 059dae63e07c): the pcs of frame_alloc_9
   that the class-9 segment cuts (lib/A/Rt/StackMalloc9Cuts.v) name. Read from the listing (internal path)
   (internal record, sha256 b69dbf0a6492) (capstone 5.0.7 over the pin, symbols of the unstripped twin 66cd0f159895):
     frame_alloc_9 = 0x3e15c, 376 B, 94 instructions                                   (PC_STACK_MALLOC_9, StackSide9.v)
       +0x98  = 0x3e1f4  the head of the 32-flag search loop (`and a7, a2, a5`)                          (PC_SM9_LOOP)
       +0xe4  = 0x3e240  the free-flag exit of that loop (`addi a2, a2, 1`, the target of `beqz t0`)     (PC_SM9_FOUND)
       +0x128 = 0x3e284  the jal into the MemToShadow copy 0x3e324 (result discarded)
       +0x138 = 0x3e294  the jal into PoisonShadow 0x551a8
       +0x13c = 0x3e298  the pc PoisonShadow returns to (`mv a0, s2`, then the epilogue)                (PC_SM9_MSRET)
   The function's own frame is `addi sp, sp, -0x30` at +0x0, released by `addi sp, sp, 0x30` at +0x154 (SM9_FRAME).

   Everything else the class-9 walk reads is the class-8 table lib/A/Rt/StackMalloc8Tbl.v, re-exported here and used
   by its names: frame_alloc_9 +0x20..+0x28 is the same TLS chain as frame_alloc_8 +0x20..+0x28 (auipc / addi of the
   .got pair 0xa26b0, `jal` into the wrapper of __tls_get_addr 0x430a4), so the chain's code ranges, its start-up cells
   (the 21 cell premises of the closed theorems) and its stack depth (SM9_WIN = SM8_WIN = 224) are the class-8 ones;
   the two callees MemToShadow (PC_MEM_TO_SHADOW = 0x3e324) and PoisonShadow (PC_POISON_SHADOW = 0x551a8) are the same
   entries, and their image-free summaries (lib/Reusable/AsStackLeaf.v) come through that file. CID9 and the class-9
   entry pcs are lib/A/Rt/StackSide9.v's, also re-exported. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Export StackSide9 StackMalloc8Tbl.
Import ListNotations.
Open Scope Z_scope.

Definition PC_SM9_LOOP : Z := 0x3e1f4.
Definition PC_SM9_FOUND : Z := 0x3e240.
Definition PC_SM9_MSRET : Z := 0x3e298.
Definition SM9_FRAME : Z := 48.
Definition SM9_WIN : Z := 224.
