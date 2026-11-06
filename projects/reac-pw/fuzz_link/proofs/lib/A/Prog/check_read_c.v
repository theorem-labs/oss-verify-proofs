(* check_read (fuzz_link.c:532-553) on image A (fuzz_link.asan 0x86930, 120 bytes; listing
   (internal path) (internal record, sha256 68ad23d44113)): a read answered the reply's code,
   and on 0 the kind and the alias of the reply. a0 = rc, a1 = want, a2 = kind, a3 = want_kind, a4 = alias, a5 = want_alias.
   `if (!same_rc(rc, want) || (rc == 0 && (strcmp(kind, want_kind) || strcmp(alias, want_alias)))) abort();` The plain
   contract is lib/Prog/check_read_c.v; this file states the same premises in link_amem.v's `aleaf_rd`
   form.

   The image-A code, in order:
     +0x00..+0x0c  push a 32-byte frame; save ra, s0, s1
     +0x10..+0x14  s0 := want_alias, s1 := alias
     +0x18..+0x1c  a4 := 0xf4240 = 1000000 = RC_FAILS (lui/addiw)
     +0x20  beq a1, a4 -> +0x30
     +0x24..+0x28  a1 := (rc xor want) <> 0; +0x2c j +0x34             (want <> RC_FAILS: abort iff rc <> want)
     +0x30  a1 := (rc = 0)                                             (want = RC_FAILS: abort iff rc = 0)
     +0x34  bnez a1 -> +0x70 (abort path)
     +0x38  bnez a0 -> +0x5c                                           (rc <> 0: no string compare; return)
     +0x3c..+0x44  wrapper_strcmp(kind, want_kind) (0x4304c);  +0x48 bnez a0 -> +0x70
     +0x4c..+0x54  wrapper_strcmp(alias, want_alias);           +0x58 bnez a0 -> +0x70
     +0x5c..+0x6c  restore, pop, ret
     +0x70  jal before_abort (0x5b318); +0x74 jal abort (0x90ac4).
   Every compare of rc and want is on the whole 64-bit registers. No instrumented check (the strings are checked
   inside the strcmp wrapper).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x0c (inside [sp - K, sp)); each strcmp call takes
     the premises of the strcmp wrapper's contract on link, lib/A/Rt/RtString.v `astrcmp_realizes` (where
     `astrcmp_arg` of index_of_c.v states them per string, the tail clause included) at sp' = sp - 32, which the
     walk derives from the journal; +0x6c ret.
   - K = 32 + 2 * ESTACK = 8224: the 32-byte frame, then the strcmp wrapper's window [sp' - 2 * ESTACK, sp'). No
     realignment. The plain K (32: strcmp counted as using no stack) does not carry over.
   - the two register conditions (the plain ones, `w64` for the plain `wz`): `want = RC_FAILS -> rc <> 0` makes the
     seqz arm give 0, `want <> RC_FAILS -> rc = want` makes the xor/snez arm give 0: +0x34 falls through.
   - only when rc = 0 (+0x38 falls through to the compares): the four C strings (`acstr_at`), each with
     `astrcmp_arg` (index_of_c.v: 0 < p, |s| + 1 < 2 ^ 32, amem_range, range_addressable, shadow_hull_vis over
     [p, p + |s| + 1), apart from this frame and the wrapper's window), and `k = k' /\ a = a'`: equal strings make
     each strcmp stop at the shared NUL with equal bytes and answer 0, so +0x48 and +0x58 fall through.
   THE ABORT PATH IS UNREACHABLE under these premises.
   The plain contract asked the four strings on every path ("keeps the premise simple"); the strings are read only
   when rc = 0, so here they are asked only then (a weaker premise, still true at the one call site, op_read
   LLVMFuzzerTestOneInput, which passes `kind ? kind : wk, wk, alias ? alias : wa, wa`, fuzz_link.c:696).
   The write set is empty. The read set (`aleaf_rd`): when rc = 0, the four strings with their NULs. EV = 0,
   SIDE = [].

   What does NOT carry over from the plain text: nothing is false of image A. The plain Post `only_frame` (True)
   stays True.
   Released proofs (rule 24): none of check_read (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038): the
   hits are generic identifiers of unrelated units).

   Satisfiability witness (op_read of "nl0", kc = ac = 16, the check_read call in LLVMFuzzerTestOneInput; run R of
   lib/A/Prog/help_witness.v): rc = want = w64 0; kind = the text_buf(16) block at 0x602000000010 holding "" (NUL at
   0, then 0x5a), alias = the second at 0x602000000040; want_kind = wk at 0x7f00000022e0 and want_alias = wa at
   0x7f0000002330, offsets 736 and 816 of the caller's class-4 side frame at 0x7f0000002000 (its frame description
   string at .rodata 0x1672f), 40 zero bytes each; the shadow with the run's values (heap chunks fa fa 00 00 01 fa;
   the side frame's wk / wa granules 0 between f2 / f3 redzones); all four outside [sp - 8224, sp) with sp =
   0x7fffffffee60. The closed lemma `check_read_apre_sat` is in lib/A/Prog/help_witness.v.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem index_of_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_READ_A : Z := 0x86930.
Lemma CHECK_READ_A_is_entry : CHECK_READ_A = LA_check_read. Proof. reflexivity. Qed.

(* the stack bound on image A: the 32-byte frame and the strcmp wrapper's window *)
Definition CHECK_READ_AFRAME : Z := 32.
Definition CHECK_READ_AK : Z := CHECK_READ_AFRAME + 2 * ESTACK.
Lemma CHECK_READ_AK_val : CHECK_READ_AK = 8224. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition check_read_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

(* a C string read through argument register i, with its NUL *)
Definition check_read_str (regs : bvmap 5 word) (m : word -> option byte) (i a : Z) : Prop :=
  exists s, acstr_at segs m (aarg regs i) s /\ aarg regs i <= a <= aarg regs i + Z.of_nat (length s).

(* the read set: the four strings, read only when rc = 0 *)
Definition check_read_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  getr regs 10 = w64 0 /\
  (check_read_str regs m 2 a \/ check_read_str regs m 3 a \/ check_read_str regs m 4 a \/ check_read_str regs m 5 a).

Definition check_read_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  (getr regs 11 = w64 RC_FAILS -> getr regs 10 <> w64 0)
  /\ (getr regs 11 <> w64 RC_FAILS -> getr regs 10 = getr regs 11)
  /\ (getr regs 10 = w64 0 -> exists k k' a a',
        acstr_at segs m (aarg regs 2) k /\ acstr_at segs m (aarg regs 3) k'
        /\ acstr_at segs m (aarg regs 4) a /\ acstr_at segs m (aarg regs 5) a'
        /\ astrcmp_arg segs regs CHECK_READ_AK m (aarg regs 2) k
        /\ astrcmp_arg segs regs CHECK_READ_AK m (aarg regs 3) k'
        /\ astrcmp_arg segs regs CHECK_READ_AK m (aarg regs 4) a
        /\ astrcmp_arg segs regs CHECK_READ_AK m (aarg regs 5) a'
        /\ k = k' /\ a = a').

(* the abort path is not taken; the plain Post `only_frame` is True *)
Definition check_read_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

Definition check_read_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B CHECK_READ_A CHECK_READ_AK 0 []
    check_read_apre check_read_ard check_read_awr check_read_apost.

End c.
