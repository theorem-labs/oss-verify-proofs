(* check_requests (fuzz_link.c:498-517, requests_are :627-637) on image A (fuzz_link.asan 0x869a8, 368 bytes; listing
   (internal path) (internal record, sha256 da0e135719be)): the operation sent exactly
   the requests it owes, in order and byte for byte. As on the plain image the C argument `&g_nl` is dropped: the code
   reads the global (+0x3c..+0x40 `auipc a4, 0x556; addi s2, a4, 0xdc` = LA_G_NL) and the one remaining argument a0 is
   the model block m. The plain contract is lib/Prog/check_requests_c.v; this file states the same premises in
   link_amem.v's `aleaf_rd` form.

   The image-A code, in order:
     +0x00..+0x28  push an 80-byte frame; save ra, s0..s8
     +0x30..+0x34, +0x44  s4 := the shadow base, loaded through the .got cell 0xa19d0 (LA_GOT_SHADOW, which holds
                   LA_SHADOW_CELL = 0xaa438, which holds the base)
     +0x48, +0x60  s5 := lw (g_nl + 0x422a8) = nk_n_sent (271016 = NK_N_SENT; a constant offset into a global,
                   unchecked)
     +0x4c..+0x5c, +0x64, +0x14c..+0x15c  the instrumented check of the 4-byte load of m->n_req at m + 0x2090 (8336 =
                   MD_N_REQ): shadow byte s = 0 passes; else (a & 7) + 3 < s passes; else errpath_load4 (0x5a45c)
     +0x68  lw a1, 0(m + 8336) = md_n_req;  +0x6c  bne s5, a1 -> +0x144 (abort path)
     +0x70  blez s5 -> +0x114                                           (no request: return)
     +0x74..+0xac  s0 := m + 12 (MD_REQ), s6 := s1 := m + 0x2010 (8208 = MD_REQ_LEN), s7 := s3 := g_nl + 0x42228
                   (270888 = NK_SENT_LEN), s2 := g_nl + 0x40224 (262692 = NK_SENT), s8 := the shadow byte address of s7
     loop, i = 0 .. n_sent - 1:
     +0xb0..+0xb4, +0x160..+0x164  the instrumented check of the 8-byte load of g_nl.sent_len[i] (register-relative, so
                   checked): shadow byte <> 0 goes to errpath_load8 (0x5a4fc), so it passes only when the byte is 0
     +0xb8..+0xc4, +0x168..+0x16c  the same check of the 8-byte load of m->req_len[i]
     +0xc8  ld a2, 0(s7) = sent_len[i];  +0xcc  ld a0, 0(s6) = req_len[i];  +0xd0  bne a2, a0 -> +0x144
     +0xd4..+0xdc  a2 := min(a2, 0x200) (unsigned)
     +0xe0..+0xe8  wrapper_bcmp(g_nl.sent[i], m->req[i], a2) (0x4305c);  +0xec  bnez a0 -> +0x144
     +0xf0..+0x110  next i (sent[i], req[i] by 0x200; the length and shadow cursors by 8 and 1)
     +0x114..+0x140  restore, pop, ret
     +0x144  jal before_abort (0x5b318); +0x148 jal abort (0x90ac4).

   Which instruction needs which premise:
   - the journal, gp/tp, ret_ok (apre): the frame stores +0x04..+0x28 (inside [sp - K, sp)); the bcmp call takes the
     premises of Reusable/YG0d.v:360-379 `abcmp_realizes` at sp' = sp - 80 (ecall_pre with its 2 * ESTACK window),
     which the walk derives from the journal; +0x140 ret.
   - K = 80 + 2 * ESTACK = 8272: the 80-byte frame, then the bcmp wrapper's window [sp' - 2 * ESTACK, sp')
     (abcmp_realizes, YG0d.v:363). No realignment. The plain K (48) does not carry over.
   - `anlk_at m LA_G_NL kbs`: +0x60 (n_sent), +0xc8 (sent_len[i]), bcmp's reads of sent[i].
   - `amodel_at m mp mbs`: +0x68 (n_req), +0xcc (req_len[i]), bcmp's reads of req[i].
   - `nlk_wf kbs`, `model_wf mbs`, `requests_are kbs mbs` (the plain three): n_sent = n_req makes +0x6c fall through
     (two sign-extended 32-bit words); 0 <= n_sent <= 16 bounds the loop inside the arrays; sent_len[i] = req_len[i]
     (64-bit words) makes +0xd0 fall through; equal first min(len, 512) bytes make bcmp answer 0 (its `v = 0 <->`
     clause), so +0xec falls through; req_len[i] <= 512 (model_wf) bounds bcmp's n below 2 ^ 32. THE ABORT PATH IS
     UNREACHABLE under these. (link-a/plan/CONTRACTS.md (internal record, sha256 5cd783c633c3) 6a, LinkHelpers: without
     the count bound of nlk_wf the loop reads past the model block.)
   - `range_addressable (ard m) SHADOW_OFF mp MD_SIZE`: the check of n_req, the checks of req_len[i] (8-byte, each a
     whole granule: the block is 16-aligned and MD_REQ_LEN = 8208 = 8 * 1026, so check_passes_whole gives shadow 0),
     and bcmp's range checks of req[i]; `shadow_hull_vis (ard m) mp MD_SIZE` and `amem_range mp MD_SIZE`: bcmp's
     hull and amem_range of req[i] (sub-ranges of the block). Stated over the whole calloc(1, 8856) block, which is
     what the caller holds (AR's block_shadow and AR_shadow_law for a heap block).
   - `range_addressable (ard m) SHADOW_OFF LA_G_NL NK_SIZE` and `shadow_hull_vis (ard m) LA_G_NL NK_SIZE`: the checks
     of sent_len[i] (NK_SENT_LEN = 270888 = 8 * 33861, LA_G_NL 64-aligned: whole granules) and bcmp's range checks and
     hull of sent[i]; stated over the whole object g_nl (NK_SIZE = 8 * 33999, whole granules), whose shadow is 0
     (an instrumented global; its redzone lies after it). bcmp's `amem_range` of sent[i] holds of the constants
     (LA_G_NL + NK_SIZE < kLowMemEnd), so it is no premise.
   - `apart_frame regs K mp MD_SIZE`: the block is outside this frame and outside bcmp's window (its two
     `~ (sp' - 2 * ESTACK <= a < sp')` premises); g_nl, an image byte, is outside both by the journal.
   - `apart_gnl mp MD_SIZE`: the plain separation, carried over in content (link-a/form/FORM.md (internal record, sha256 13aeff774164) 1a).
   The write set is empty. The read set (`aleaf_rd`): the model block read through the argument, [mp, mp + MD_SIZE).
   EV = 0 (no allocator event), SIDE = [] (no frame_alloc).

   What does NOT carry over from the plain text:
   - `frame_apart_gnl regs 48` (link-a/form/FORM.md (internal record, sha256 13aeff774164) 1a): the window is on the
     real stack above alloc_ceiling (the journal's `astk_ok`, YCbq.v:330-332) and g_nl is an image byte.
   The plain Post `only_frame` (True) stays True.
   Released proofs (rule 24): none of check_requests (link-a/index/SUMMARY.md (internal record, sha256 58ab2c29f038)).

   Satisfiability witness (op_read of "nl0" as the first op, the check_requests call in LLVMFuzzerTestOneInput after
   check_read; run R of lib/A/Prog/help_witness.v): g_nl after the exchange: n_sent = 1, sent_len[0] = 32, sent[0] =
   link_spec `req_read 2` (the RTM_GETLINK for index_of "nl0" = 2); the model block (calloc(1, 8856) at
   0x602000001000): next = 1 (talk took chunk 0), n_req = 1, req_len[0] = 32, req[0] the same 32 bytes, every other
   field 0; the shadow with the run's values (g_nl's 33999 granules 0; the model block's granules 0); sp =
   0x7fffffffee60. The closed lemma `check_requests_apre_sat` is in lib/A/Prog/help_witness.v.
   Proves no function (kind: statement text). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YI16 YM05 YG0v YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_REQUESTS_A : Z := 0x869a8.
Lemma CHECK_REQUESTS_A_is_entry : CHECK_REQUESTS_A = LA_check_requests. Proof. reflexivity. Qed.

(* the stack bound on image A: the 80-byte frame and the bcmp wrapper's window *)
Definition CHECK_REQUESTS_AFRAME : Z := 80.
Definition CHECK_REQUESTS_AK : Z := CHECK_REQUESTS_AFRAME + 2 * ESTACK.
Lemma CHECK_REQUESTS_AK_val : CHECK_REQUESTS_AK = 8272. Proof. reflexivity. Qed.

(* the write set: nothing outside the frame *)
Definition check_requests_awr (regs : bvmap 5 word) (m : word -> option byte) : list (Z * Z) := [].

(* the read set: the model block *)
Definition check_requests_ard (regs : bvmap 5 word) (m : word -> option byte) (a : Z) : Prop :=
  rd_ivl (aarg regs 0) (aarg regs 0 + MD_SIZE) a.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variables rlo rhi : Z.
Variable B : asyms.

Definition check_requests_apre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists kbs mbs,
    anlk_at segs m LA_G_NL kbs /\ amodel_at segs m (aarg regs 0) mbs
    /\ nlk_wf kbs /\ model_wf mbs /\ requests_are kbs mbs
    /\ range_addressable (ard segs m) SHADOW_OFF (aarg regs 0) MD_SIZE
    /\ shadow_hull_vis (ard segs m) (aarg regs 0) MD_SIZE
    /\ amem_range (aarg regs 0) MD_SIZE
    /\ range_addressable (ard segs m) SHADOW_OFF LA_G_NL NK_SIZE
    /\ shadow_hull_vis (ard segs m) LA_G_NL NK_SIZE
    /\ apart_frame regs CHECK_REQUESTS_AK (aarg regs 0) MD_SIZE
    /\ apart_gnl LA_G_NL (aarg regs 0) MD_SIZE.

(* the abort path is not taken; the plain Post `only_frame` is True *)
Definition check_requests_apost (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop := True.

Definition check_requests_acontract : Prop :=
  aleaf_rd SK segs rlo rhi B CHECK_REQUESTS_A CHECK_REQUESTS_AK 0 []
    check_requests_apre check_requests_ard check_requests_awr check_requests_apost.

End c.
