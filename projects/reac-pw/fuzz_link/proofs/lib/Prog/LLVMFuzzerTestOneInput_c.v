(* LLVMFuzzerTestOneInput (fuzz_link.c:764-790): the slot. One driver call runs at most 48
   operations and answers 0.

   The contract is exactly the obligation the frame asks of this entry (lib/FrameAPI.v frame_plain,
   ENTRY = 0x1384c, SLOT_STACK = 65536, for every j below 4), in the frame's T form (lib/Reusable/YL0i.v
   lib_contract_x_T) at the memory-FILE shape (lib/MemFileRI.v mf_shape): link's slot leaves ONE heap block
   live across driver calls, the FILE mark_quietly opens with fmemopen and never closes (1304 bytes,
   lib/MemFile.v MF_BLOCK), so the post accounts kept blocks T -> T' instead of returning the allocator to
   its entry bound. The bindings and the globals list are link's:
   - llvm_G: the image bytes one call may change: __stderr_FILE + 136 (its orientation; kept from the frame's
     list, link writes no stderr), g_nl, g_names, msg_build.long_alias, g_sink, g_said, g_say and musl's
     open-file list head ofl_head (fmemopen -> __ofl_add writes it). It is the frame lane's frame_G.
   - llvm_GI: the global invariant over the kept blocks is the memory FILE's (lib/MemFile.v mf_gi): before
     the first mark g_sink = g_say = ofl_head = 0 and T = []; from then on they all hold f, T = [(f, 1304)],
     and f is a memory FILE over g_said. With it, the NUL at long_alias[300] (0x743f8 + 300): kernel's
     msg_build fills long_alias[0..300) and calls strlen on it (kernel_c.v Pre), and long_alias is in G,
     so nothing else carries that byte from one driver call to the next.
   - the output function is fun _ => []: the slot writes nothing (its printf goes to the memory FILE).
   Restated by the slot lane (a Theorem Labs lane) to the frame's new obligation (a Theorem Labs lane 2026-10-30, decision 4;
   link/ct/AMEND-slot.md item 4); the earlier text was lib_contract_o (no kept block) with pcap's G.
   Entry and bindings read from the plain image (the unstripped twin of the pin ebe34b259b9f). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Mem.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_ENTRY : Z := 0x1384c.
Definition LLVM_FRAME : Z := 480.
(* the deepest call: reac_served_unmark_all's 17232 below the slot's 480 *)
Definition LLVM_K : Z := 17760.
Definition LLVM_MALLOC : Z := 0x17514.
Definition LLVM_FREE : Z := 0x173d4.
Definition LLVM_CALLOC : Z := 0x1729c.
Definition LLVM_GUARD_GOT : Z := 0x208d8.
Definition LLVM_GUARD : Z := 0x95878.
Definition LLVM_TP : Z := 0x75608.
Definition MODEL_BYTES : Z := 8856.
Definition MARKS_BYTES : Z := 516.

Lemma LLVM_K_fits : LLVM_K <= SLOT_STACK.
Proof. unfold LLVM_K, SLOT_STACK. lia. Qed.

(* = lib/FrameAPI.v frame_G (the frame lane's list, 3affacb2053) *)
Definition llvm_G : list (Z * Z) := frame_G.

Section K.
Variable B : malloc_syms.
Context {SH : sink_head}.

Definition llvm_GI : nat -> list (Z * Z) -> (word -> option byte) -> Prop :=
  fun _ T m => mf_gi B link_mf T m /\ Mem.bytes_at rsegs m (0x743f8 + 300) [Z_to_bv 8 0].

End K.

(* THE CONTRACT: what the frame asks of ENTRY (lib/FrameAPI.v frame_plain_mf, its last premise), with link's
   G, GI and output, under the frame's own facts of the allocator, the sink and the image
   (FrameAPI.frame_facts_plain at mf_shape: the bindings, the static addresses, frame_allocator at every
   RunCeil and FP state). *)
Definition LLVMFuzzerTestOneInput_contract (B : malloc_syms) (APIf : forall rc : YM05.RunCeil, AllocAPI B)
    (SH : sink_head) (SK : sink_syms) : Prop :=
  forall ra empty, frame_facts_plain B APIf mf_shape SH SK ra empty ->
  forall (rc : YM05.RunCeil) (fx : YK11.FPState) (j : nat), (j < 4)%nat ->
    @lib_contract_x_T fx rc mf_shape B (APIf rc) SH SK llvm_G frame_RELRO (@llvm_GI B SH) (fun _ => []) j
      LLVM_ENTRY ra empty SLOT_STACK.
