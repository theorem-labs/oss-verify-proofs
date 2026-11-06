(* check_marks (fuzz_link.c:608-623, marks_are :644-652) on image A (fuzz_link.asan 0x8848c, 208 bytes; listing
   (internal path) (internal record, sha256 0a5790c7d7c2)): the marks kept are the interfaces
   this daemon marked, each once, in the model order. a0 = got (struct reac_served_marks), a1 = m (struct model). The
   plain contract is lib/Prog/check_marks_c.v; this file states the same premises in link_amem.v's `aleaf_rd` form.

   The image-A code, in order:
     +0x00..+0x10  push a 32-byte frame; save ra, s0, s1, s2
     +0x14..+0x1c  a3 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     +0x20..+0x2c, +0xac..+0xb8  the instrumented check of the 4-byte load of got->n at got: shadow byte s = 0 passes;
                   else (got & 7) + 3 < s passes; else errpath_load4 (0x5a45c)
     +0x30..+0x44, +0x4c, +0xbc..+0xcc  the same check of the 4-byte load of m->n_mark at m + 0x2294 (8852 = MD_N_MARK)
     +0x48  lw s2, 0(got) = got->n;  +0x50  lw a2, 0(m + 8852) = m->n_mark;  +0x54  bne s2, a2 -> +0xa4 (abort path)
     +0x58  blez s2 -> +0x8c                                            (no mark: return)
     +0x5c..+0x68  s0 := got + 4 (MK_NAME), s1 := m + 0x2094 (8340 = MD_MARK)
     loop, i = 0 .. n - 1:
     +0x6c..+0x74  wrapper_strcmp(got->name[i], m->mark[i]) (0x4304c);  +0x78  bnez a0 -> +0xa4
     +0x7c..+0x88  next i (both slots by 16)
     +0x8c..+0xa0  restore, pop, ret
     +0xa4  jal before_abort (0x5b318); +0xa8 jal abort (0x90ac4).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x10 (inside [sp - K, sp)); each strcmp call takes
     the premises of the strcmp wrapper's contract on link, lib/A/Rt/RtString.v `astrcmp_realizes` (from
     pcap's Reusable/AStrcmpDef.v without the tail clause), at sp' = sp - 32, which the walk derives from the
     journal; +0xa0 ret.
   - K = 32 + 2 * ESTACK = 8224: the 32-byte frame, then the strcmp wrapper's window [sp' - 2 * ESTACK, sp'). No
     realignment. The plain K (32: strcmp counted as using no stack) does not carry over.
   - `amarks_at m got gbs`, `amodel_at m mp mbs`: the loads +0x48, +0x50 and the strings strcmp reads.
   - `marks_wf gbs`, `model_marks_wf mbs` (0 <= n <= MARKS_MAX, a NUL inside each of the first n 16-byte slots:
     each strcmp stops inside its slot), `marks_are gbs mbs` (got->n = m->n_mark makes +0x54 fall through, two
     sign-extended 32-bit words; equal slot strings make each strcmp answer 0, so +0x78 falls through). THE ABORT
     PATH IS UNREACHABLE under these.
   - `range_addressable (ard m) SHADOW_OFF got MK_SIZE`, `shadow_hull_vis (ard m) got MK_SIZE`,
     `amem_range got MK_SIZE`: the check +0x20 of got->n, and every strcmp's checks of got->name[i] up to its NUL
     (sub-ranges of the block; the strcmp wrapper's `0 < x` holds since x = got + 4 + 16 i, and its
     `k + 1 < 2 ^ 32` since k < 16). Stated over the whole calloc(1, 516) block the caller holds.
   - the same three over the model block [mp, mp + MD_SIZE): the check of m->n_mark and the strcmp checks of
     m->mark[i].
   - the strcmp wrapper's `atail_vis` of each slot string (the bytes after its NUL to the end of its 8-byte granule
     visible): inside the block for every slot but the last of the marks block, whose granule may end past the
     516-byte block (516 = 8 * 64 + 4; the slot is [got + 500, got + 516)), hence `ard m b <> None` for
     got + MK_SIZE <= b < the end of that granule (the chunk's tail, present by AR's chunk areas at the caller).
     The model block's mark slots get the symmetric clause past [mp, mp + MD_SIZE) (comparer: 8856 ends on a granule
     only when mp mod 8 = 0, which the Pre does not state; for the calloc'd, 16-aligned block the range is empty).
   - `apart_frame regs K got MK_SIZE`, `apart_frame regs K mp MD_SIZE` (the plain two, with image A's K): outside this
     frame and outside the strcmp wrapper's window.
   The write set is empty. The read set (`aleaf_rd`): the two blocks read through the arguments. EV = 0, SIDE = [].

   What does NOT carry over from the plain text: nothing is false of image A. The plain Post `only_frame` (True)
   stays True.
   Released proofs (rule 24): none of check_marks (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).

   Satisfiability witness (op_mark of "nl0" as the first op, two ACK chunks, the check_marks call in
   LLVMFuzzerTestOneInput; run M of lib/A/Prog/help_witness.v): the marks block (calloc(1, 516) at 0x602000004000)
   with n = 1 and name[0] = "nl0", the rest 0; the model block (0x602000001000) with n_mark = 1, mark[0] = "nl0",
   next = 2, n_req = 2, req[0] = req_read 2, req[1] = req_write 2 "reac-pw:served", req_len 32 and 52, the rest 0;
   the shadow with the run's values (marks: 64 granules 0, then 04; model: granules 0); sp = 0x7fffffffee60. The
   closed lemma `check_marks_apre_sat` is in lib/A/Prog/help_witness.v.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_MARKS_A : Z := 0x8848c.
Lemma CHECK_MARKS_A_is_entry : CHECK_MARKS_A = LA_check_marks. Proof. reflexivity. Qed.

(* the stack bound on image A: the 32-byte frame and the strcmp wrapper's window *)
Definition CHECK_MARKS_AFRAME : Z := 32.
Definition CHECK_MARKS_AK : Z := CHECK_MARKS_AFRAME + 2 * ESTACK.
Lemma CHECK_MARKS_AK_val : CHECK_MARKS_AK = 8224. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition check_marks_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

(* the read set: the marks block and the model block *)
Definition check_marks_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  rd_ivl (aarg regs 0) (aarg regs 0 + MK_SIZE) a \/ rd_ivl (aarg regs 1) (aarg regs 1 + MD_SIZE) a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition check_marks_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists gbs mbs,
    amarks_at segs m (aarg regs 0) gbs /\ amodel_at segs m (aarg regs 1) mbs
    /\ marks_wf gbs /\ model_marks_wf mbs /\ marks_are gbs mbs
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) MK_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) MK_SIZE
    /\ amem_range (aarg regs 0) MK_SIZE
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 1) MD_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 1) MD_SIZE
    /\ amem_range (aarg regs 1) MD_SIZE
    /\ apart_frame regs CHECK_MARKS_AK (aarg regs 0) MK_SIZE
    /\ apart_frame regs CHECK_MARKS_AK (aarg regs 1) MD_SIZE
    /\ (forall b, aarg regs 0 + MK_SIZE <= b < (aarg regs 0 + MK_SIZE + 7) / 8 * 8 -> ard segs m b <> None)
    /\ (forall b, aarg regs 1 + MD_SIZE <= b < (aarg regs 1 + MD_SIZE + 7) / 8 * 8 -> ard segs m b <> None).

(* the abort path is not taken; the plain Post `only_frame` is True *)
Definition check_marks_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

Definition check_marks_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B CHECK_MARKS_A CHECK_MARKS_AK 0 []
    check_marks_apre check_marks_ard check_marks_awr check_marks_apost.

End c.
