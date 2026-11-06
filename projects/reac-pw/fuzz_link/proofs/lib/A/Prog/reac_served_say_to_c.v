(* reac_served_say_to (reac_served_mark.c:16-19) on image A (fuzz_link.asan 0x89504, 12 bytes, 3 instructions;
   listing (internal path) (internal record, sha256 52363ef41162)): point the
   policy's stream at `out`. The plain contract is lib/Prog/reac_served_say_to_c.v; this file states the SAME link_spec
   result in link_amem.v's `aleaf` form.

   The whole function on image A is
     +0x00  auipc a1, 0x5a8
     +0x04  sd a0, -0x224(a1)                                    ; = 0x6312e0 = LA_G_SAY, the .bss word g_say
     +0x08  ret
   No frame, no call, no instrumented check: the store goes to a constant offset into a global, which the instrumentation
   leaves unchecked (link-a/facts/asan-facts.tsv (internal record, sha256 05ab19b7928f): frame 0, checks 0, errpath_calls 0, no
   callee). The harness reaches it once per process, from mark_quietly 0x8841c, with the FILE fmemopen made (fuzz_link.c:160).

   Which instruction needs which premise:
   - the journal (apre's first conjunct): the store changes memory and the Post re-states the caller's journal;
     its AR is untouched (no shadow byte, no allocator byte is written).
   - `awrange segs m LA_G_SAY 8`: the store +0x04 needs those 8 bytes writable (the plain `wr_at`).
   - the write set [LA_G_SAY, LA_G_SAY + 8) and apre's `ajw` on it: that one store. g_say is an image byte, so `ajw`
     holds of it only through `inG G`: the caller's journal must carry g_say in its program globals. It does: `LA_G` of
     link_aaddr.v holds (LA_G_SAY, 8) (the ruling of link-a/form/FORM.md (internal record, sha256 13aeff774164) section 7).
   - registers: +0x04 stores a0 whole (the Post's `aarg regs 0`); +0x08 `ret` (apost's return to `getr regs 1`,
     with `YK0s.ret_ok`).
   - K = 0: no frame, no call. The plain K is 0 too.
   - no read set: the function dereferences no pointer argument, so this is the plain `aleaf` shape and not
     `aleaf_rd`. a0 is stored as a value, never read through.
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   Plain premises and Post conjuncts that carry over unchanged in content: all of them. Nothing of the plain text
   is false of image A (the plain contract claims no `m' = m`; there is no frame to push).
   Released proofs (rule 24): none of reac_served_say_to
   (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition REAC_SERVED_SAY_TO_A : Z := 0x89504.
Lemma REAC_SERVED_SAY_TO_A_is_entry : REAC_SERVED_SAY_TO_A = LA_reac_served_say_to. Proof. reflexivity. Qed.

(* the stack bound on image A: no frame, no call *)
Definition REAC_SERVED_SAY_TO_AK : Z := 0.

(* the write set: the 8-byte word g_say *)
Definition reac_served_say_to_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) :=
  [(LA_G_SAY, LA_G_SAY + 8)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition reac_served_say_to_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  awrange segs m LA_G_SAY 8.

Definition reac_served_say_to_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  au64_at segs m' LA_G_SAY (aarg regs 0).

Definition reac_served_say_to_acontract : Prop :=
  aleaf SK segs rlo rhi B REAC_SERVED_SAY_TO_A REAC_SERVED_SAY_TO_AK 0 []
    reac_served_say_to_apre reac_served_say_to_awr reac_served_say_to_apost.

End c.
