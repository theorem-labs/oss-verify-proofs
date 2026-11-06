(* fuzz_close (netlink.h:139-146) on image A (fuzz_link.asan 0x8267c, 80 bytes, 20 instructions; listing
   (internal path) (internal record, sha256 da666a6f173e)): the fake close(). It marks the
   socket shut and counts the close. The plain contract is lib/Prog/fuzz_close_c.v; this file states the SAME link_spec
   result in link_amem.v's `aleaf` form.

   The image-A code has no frame, no call and no instrumented check: g_nl's three fields are loaded and stored at
   constant offsets from the address the code forms (+0x04..+0x08 `auipc a1, 0x55a; addi a1, a1, 0x440` =
   LA_G_NL), and the instrumentation leaves an access at a constant offset into a global unchecked. So the contract
   needs no shadow premise and no side-stack room, and K = 0 (the plain K is 0 too: the plain code has the same
   shape).

   Which instruction needs which premise:
   - the journal (apre's first conjunct): every store below changes memory, and the Post re-states the caller's
     journal; its AR is untouched (no shadow, no allocator byte is written).
   - `exists bs, anlk_at m LA_G_NL bs`: the loads +0x18 `lw a0, 0x214(a0)` (open, read only when a0 = 7) and +0x38
     `lw a1, 0x21c(a0)` (closed) read g_nl.open and g_nl.closed; the stores +0x2c `sw a2, 0x220(a0)` (misuse := 1),
     +0x40 `sw zero, 0x214(a0)` (open := 0) and +0x44 `sw a1, 0x21c(a0)` (closed := closed + 1) need those bytes
     writable. 0x40000 + 0x214 = 262676 = NK_OPEN, + 0x21c = NK_CLOSED, + 0x220 = NK_MISUSE (link_spec.v:713-716).
   - `nlk_wf bs`: carried for the Post's `nlk_wf bs'` (the stores keep open in 0..1 and misuse in 0..1).
   - `nk_closed bs + 1 < 2 ^ 31`: +0x3c `addi a1, a1, 1` then the 4-byte store; the bound keeps the Post's
     `nk_closed bs' = nk_closed bs + 1` exact and nlk_wf's `nk_closed < 2 ^ 31` true.
   - the write set [LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4) and apre's `ajw` on it: the three stores. Those bytes
     are image bytes, so `ajw` holds of them only through `inG G`: the caller's journal must have g_nl's open ..
     misuse fields in its program-global ranges G.
   - registers: +0x0c `bne a0, a2` compares the whole 64-bit a0 with 7 (Post's `aarg regs 0 =? NL_FD`); +0x48
     `mv a0, zero` (Post's a0 = 0); +0x4c `ret` (apost's return to `getr regs 1`; `YK0s.ret_ok`).
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   Plain premises and Post conjuncts that carry over unchanged in content: all of them. Nothing of the plain text
   is false of image A.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition FUZZ_CLOSE_A : Z := 0x8267c.
Lemma FUZZ_CLOSE_A_is_entry : FUZZ_CLOSE_A = LA_fuzz_close. Proof. reflexivity. Qed.

(* the stack bound on image A: no frame, no call *)
Definition FUZZ_CLOSE_AK : Z := 0.

(* the write set: g_nl's open, opened, closed and misuse words (as the plain contract's) *)
Definition fuzz_close_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_NL + NK_OPEN, LA_G_NL + NK_MISUSE + 4)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition fuzz_close_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists bs, anlk_at segs m LA_G_NL bs /\ nlk_wf bs /\ nk_closed bs + 1 < 2 ^ 31.

Definition fuzz_close_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall bs, anlk_at segs m LA_G_NL bs -> exists bs', anlk_at segs m' LA_G_NL bs'
    /\ nlk_wf bs' /\ getr regs' 10 = w64 0
    /\ nk_open bs' = 0 /\ nk_opened bs' = nk_opened bs
    /\ nk_closed bs' = nk_closed bs + 1
    /\ nk_misuse bs' =
         (if (aarg regs 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1).

Definition fuzz_close_acontract : Prop :=
  aleaf SK segs rlo rhi B FUZZ_CLOSE_A FUZZ_CLOSE_AK 0 [] fuzz_close_apre fuzz_close_awr fuzz_close_apost.

End c.
