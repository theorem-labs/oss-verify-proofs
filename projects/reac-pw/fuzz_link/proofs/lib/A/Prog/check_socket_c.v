(* check_socket (fuzz_link.c:487-496) on image A (fuzz_link.asan 0x86734, 80 bytes; listing
   (internal path) (internal record, sha256 4590cb3f5380)): every socket opened was
   closed, and no other descriptor was used. The plain contract is lib/Prog/check_socket_c.v; this file states the same
   premise in link_amem.v's `aleaf` form. As on the plain image the C argument `&g_nl` is dropped: the code reads the
   global (+0x0c..+0x10 `auipc a0, 0x556; addi a0, a0, 0x380` = LA_G_NL) and the call sites pass no argument.

   The image-A code, in order:
     +0x00..+0x04  push a 16-byte frame; save ra                       (BEFORE the first test, unlike the plain code)
     +0x08..+0x14  a1 := g_nl + 0x40000
     +0x18  lw a2, 0x214(a1) = g_nl.open;    +0x1c bnez a2 -> +0x48 (abort path)
     +0x20  lw a2, 0x218(a1) = g_nl.opened;  +0x24 lw a1, 0x21c(a1) = g_nl.closed;  +0x28 bne a2, a1 -> +0x48
     +0x2c..+0x34  lw a0, 0x220(g_nl + 0x40000) = g_nl.misuse;  +0x38 bnez a0 -> +0x48
     +0x3c..+0x44  restore ra, pop, ret
     +0x48  jal before_abort (0x5b318); +0x4c jal abort (0x90ac4).
   0x40000 + 0x214 = 262676 = NK_OPEN, + 0x218 = NK_OPENED, + 0x21c = NK_CLOSED, + 0x220 = NK_MISUSE
   (link_spec.v:713-716). Every load is at a constant offset into a global, so the instrumentation leaves it
   unchecked: no shadow premise.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame store +0x04 (inside [sp - K, sp)); +0x44 ret.
   - K = 16: the frame pushed at +0x00, which precedes the first test (+0x1c). No callee on the returning path
     (before_abort and abort are on the abort path only, which the Pre makes unreachable). The plain K (0) does not
     carry over: the plain code pushed its frame only on the abort path.
   - `anlk_at m LA_G_NL bs`: the four loads +0x18, +0x20, +0x24, +0x34.
   - THE ABORT PATH IS UNREACHABLE: `nk_open bs = 0` makes +0x1c fall through (the sign-extended word is 0 iff the
     32-bit word is 0); `nk_opened bs = nk_closed bs` makes +0x28 fall through (two sign-extended 32-bit words are
     equal iff the words are); `nk_misuse bs = 0` makes +0x38 fall through.
   The write set is empty. EV = 0 (no allocator event), SIDE = [] (no frame_alloc). The function reads through no
   pointer argument (g_nl is an image global, kept by `akept`'s image clause), so plain `aleaf`.

   What does NOT carry over from the plain text:
   - the plain Post `unchanged` (m' = m): FALSE on image A, the returning path stores ra at sp - 8 (+0x04). The A
     Post says nothing of memory beyond `akept` (everything outside [sp - 16, sp) kept), as the plain `only_frame`
     contracts do.
   Released proofs (rule 24): none of check_socket (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038): the
   hits are unrelated units' identifiers).

   Satisfiability witness (the call LLVMFuzzerTestOneInput 0x836b0 in op_read, after reac_link_alias_read): g_nl after
   one exchange and its close: open = 0, opened = closed = 1, misuse = 0 (nl_talk closed the socket at 0x88e54;
   fuzz_close sets open := 0, closed := closed + 1 and leaves misuse 0 for fd 7 with open = 1). The closed lemma of
   `check_socket_apre` at that g_nl is in lib/A/Prog/help_witness.v.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_SOCKET_A : Z := 0x86734.
Lemma CHECK_SOCKET_A_is_entry : CHECK_SOCKET_A = LA_check_socket. Proof. reflexivity. Qed.

(* the stack bound on image A: the 16-byte frame pushed before the first test *)
Definition CHECK_SOCKET_AFRAME : Z := 16.
Definition CHECK_SOCKET_AK : Z := CHECK_SOCKET_AFRAME.
Lemma CHECK_SOCKET_AK_val : CHECK_SOCKET_AK = 16. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition check_socket_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition check_socket_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs, anlk_at segs m LA_G_NL bs
    /\ nk_open bs = 0 /\ nk_opened bs = nk_closed bs /\ nk_misuse bs = 0.

(* the abort path is not taken; nothing is promised of memory beyond akept (the plain `unchanged` is false here) *)
Definition check_socket_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

Definition check_socket_acontract : Prop :=
  aleaf SK segs rlo rhi B CHECK_SOCKET_A CHECK_SOCKET_AK 0 [] check_socket_apre check_socket_awr check_socket_apost.

End c.
