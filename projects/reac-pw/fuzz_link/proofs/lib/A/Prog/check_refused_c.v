(* check_refused (fuzz_link.c:519-530) on image A (fuzz_link.asan 0x8688c, 32 bytes; listing
   (internal path) (internal record, sha256 ac011e524e6c)): a read or a write that was
   refused opened no socket. `if (opened != opened_before) abort();` with a0 = opened_before, a1 = opened. The plain
   contract is lib/Prog/check_refused_c.v; this file states the same premise in link_amem.v's `aleaf` form.

   The image-A code, in order:
     +0x00..+0x04  push a 16-byte frame; save ra                       (BEFORE the test, unlike the plain code)
     +0x08  bne a1, a0 -> +0x18 (abort path)                           (the whole 64-bit registers)
     +0x0c..+0x14  restore ra, pop, ret
     +0x18  jal before_abort (0x5b318); +0x1c jal abort (0x90ac4).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame store +0x04 (inside [sp - K, sp)); +0x14 ret.
   - K = 16: the frame pushed at +0x00, which precedes the test (+0x08). No callee on the returning path. The plain
     K (0) does not carry over.
   - THE ABORT PATH IS UNREACHABLE: `getr regs 10 = getr regs 11` makes +0x08 fall through; the branch compares the
     whole registers, so the premise does too (both callers load the two ints with `lw`, sign-extended:
     LLVMFuzzerTestOneInput 0x836e4..0x836ec in op_read, and the op_write site).
   The write set is empty and nothing is read through a pointer: plain `aleaf`. EV = 0, SIDE = [].

   What does NOT carry over from the plain text:
   - the plain Post `unchanged` (m' = m): FALSE on image A, the returning path stores ra at sp - 8 (+0x04). The A
     Post promises nothing of memory beyond `akept`.
   Released proofs (rule 24): none of check_refused (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).

   Satisfiability witness (op_read, LLVMFuzzerTestOneInput 0x836ec): a0 = a1 = w64 1 (g_nl.opened before and after a
   refused read, both 1 after the earlier exchange). The closed lemma is in lib/A/Prog/help_witness.v.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_REFUSED_A : Z := 0x8688c.
Lemma CHECK_REFUSED_A_is_entry : CHECK_REFUSED_A = LA_check_refused. Proof. reflexivity. Qed.

(* the stack bound on image A: the 16-byte frame pushed before the test *)
Definition CHECK_REFUSED_AFRAME : Z := 16.
Definition CHECK_REFUSED_AK : Z := CHECK_REFUSED_AFRAME.
Lemma CHECK_REFUSED_AK_val : CHECK_REFUSED_AK = 16. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition check_refused_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

Definition check_refused_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  getr regs 10 = getr regs 11.

(* the abort path is not taken; nothing is promised of memory beyond akept (the plain `unchanged` is false here) *)
Definition check_refused_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition check_refused_acontract : Prop :=
  aleaf SK segs rlo rhi B CHECK_REFUSED_A CHECK_REFUSED_AK 0 []
    check_refused_apre check_refused_awr check_refused_apost.

End c.
