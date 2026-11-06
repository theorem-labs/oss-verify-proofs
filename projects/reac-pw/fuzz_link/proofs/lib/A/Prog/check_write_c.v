(* check_write (fuzz_link.c:568-577) and check_mark (:595-606) on image A (fuzz_link.asan 0x88398 and 0x88450, 60
   bytes each; listings (internal path) (internal record, sha256 aa7920dd2ebb) and
   (internal path) (internal record, sha256 02dda35ead16)): the code the call answered is
   the code the model owes, under the harness's own comparison same_rc (:476-479). The plain contract is
   lib/Prog/check_write_c.v (one statement for both); this file states the same premise in link_amem.v's `aleaf` form.

   ONE STATEMENT, TWO ENTRIES: the two listings have the same instruction words at every offset but the two jal at
   +0x34 and +0x38, which resolve to the same targets (before_abort 0x5b318, abort 0x90ac4). So the statement is
   `check_rc_acontract pc`, instantiated at each entry (check_mark_acontract is in check_mark_c.v).

   The image-A code, in order (a0 = rc, a1 = want):
     +0x00..+0x04  push a 16-byte frame; save ra                       (BEFORE the test, unlike the plain code)
     +0x08..+0x0c  a2 := 0xf4240 = 1000000 = RC_FAILS (lui/addiw)
     +0x10  beq a1, a2 -> +0x20
     +0x14..+0x18  a0 := (a0 xor a1) <> 0; +0x1c j +0x24               (want <> RC_FAILS: abort iff rc <> want)
     +0x20  a0 := (a0 = 0)                                             (want = RC_FAILS: abort iff rc = 0)
     +0x24  bnez a0 -> +0x34 (abort path)
     +0x28..+0x30  restore ra, pop, ret
     +0x34  jal before_abort (0x5b318); +0x38 jal abort (0x90ac4).
   Every compare is on the whole 64-bit registers.

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame store +0x04 (inside [sp - K, sp)); +0x30 ret.
   - K = 16: the frame pushed at +0x00, which precedes the test (+0x24). No callee on the returning path. The plain
     K (0) does not carry over.
   - THE ABORT PATH IS UNREACHABLE: `same_rc_aregs regs`: when a1 = w64 RC_FAILS, a0 <> w64 0 (the seqz arm gives
     0); otherwise a0 = a1 (the xor/snez arm gives 0). This is the plain `same_rc_regs` with `w64` for the plain
     `wz` (the same Z_to_bv 64); the caller gets it from link_spec write_agree / mark_agree.
   The write set is empty and nothing is read through a pointer: plain `aleaf`. EV = 0, SIDE = [].

   What does NOT carry over from the plain text:
   - the plain Post `unchanged` (m' = m): FALSE on image A, the returning path stores ra at sp - 8 (+0x04). The A
     Post promises nothing of memory beyond `akept`.
   Released proofs (rule 24): none of check_write or check_mark (link-a/index/SUMMARY.md
   (internal record, sha256 58ab2c29f038): the check_write hits are unrelated units' identifiers).

   Satisfiability witness (op_write in LLVMFuzzerTestOneInput, the check_write call): a0 = a1 = w64 (-22), the -EINVAL
   both model_write and reac_link_alias_write answer for a NULL name (name_of's 255). The closed lemma is in
   lib/A/Prog/help_witness.v.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_WRITE_A : Z := 0x88398.
Lemma CHECK_WRITE_A_is_entry : CHECK_WRITE_A = LA_check_write. Proof. reflexivity. Qed.

(* the stack bound on image A: the 16-byte frame pushed before the test *)
Definition CHECK_RC_AFRAME : Z := 16.
Definition CHECK_RC_AK : Z := CHECK_RC_AFRAME.
Lemma CHECK_RC_AK_val : CHECK_RC_AK = 16. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition check_rc_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

(* the register-level reading of same_rc(got, want) = 1 (the plain same_rc_regs) *)
Definition same_rc_aregs (regs : bvmap 5 word) : Prop :=
  (getr regs 11 = w64 RC_FAILS -> getr regs 10 <> w64 0)
  /\ (getr regs 11 <> w64 RC_FAILS -> getr regs 10 = getr regs 11).

Definition check_rc_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop := same_rc_aregs regs.

(* the abort path is not taken; nothing is promised of memory beyond akept (the plain `unchanged` is false here) *)
Definition check_rc_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition check_rc_acontract (pc : Z) : Prop :=
  aleaf SK segs rlo rhi B pc CHECK_RC_AK 0 [] check_rc_apre check_rc_awr check_rc_apost.

Definition check_write_acontract : Prop := check_rc_acontract CHECK_WRITE_A.

End c.
