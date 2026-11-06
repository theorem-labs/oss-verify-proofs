(* m_refuse (fuzz_segconf.c:101-111; fuzz_segconf.asan 0x877d0, 308 bytes, 77 instructions; frame 48 bytes, no
   side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form
   (afn_pre at the entry, SRr of apost_baseF at the return: it reaches snprintf).
   Functional content: the plain contract lib/Prog/m_refuse_c.v:10-78 (m_refuse_pre :50-56, m_refuse_W
   :59-65, the post :72-76), restated over the ASan reader. The post is the plain one: the block holds
   SegModel.m_refuse mc line knock (sa_mconf, the knock flag of kept[n_kept] now part of mc_kept). knock is the
   pending flag of sa_mconfp at the entry: true only at m_file's knock branch, which stores kept_knock[n_kept] = 1
   (sw 0x86b84) just before the call; m_refuse never writes kept_knock.
   What the code does (objdump of fuzz_segconf.asan, 0x877d0-0x87900): s1 = c + 0x23ac = &n_kept; n_kept = lw
   0(s1) (0x8781c); 7 < n_kept (signed blt 0x87824) skips to refused++; else a0 = c + 0x200c + 112 n_kept =
   &kept[n_kept] (0x87828-0x87844), a3 = c + 0x23b4 = c->reading, and line > 0 calls snprintf(a0, 112, .str.6, a3,
   line) (jal 0x8785c; image A .str.6 0x210c0, SegModel.F_addr_line), line <= 0 calls snprintf(a0, 112, .str.7, a3)
   (jal 0x87870; .str.7 0x210e0, SegModel.F_addr); then n_kept++ (0x8787c-0x87884); refused++ (lw/addi/sw of
   c + 0x2008, 0x878a0-0x878a8). It reads n_kept, refused, the reading string (snprintf's %s, with its slack: the
   reading field ends at the end of the 9236-byte block, so the slack is up to 4 bytes past it) and the format
   literal; it writes kept[n_kept] and n_kept when n_kept < 8, and refused: its footprint is the plain m_refuse_W
   without its first range (sp - M_REFUSE_STACK, sp), which is the call's own stack window here. No abort site
   (segA/evidence/program.asan.tsv line 16).
   What it reads besides: the shadow base, through the GOT word as_got_shadow B (image A 0xa2a50, ld at 0x877f4),
   whose value and target AR gives (AR_const_law, lib/Reusable/YG0d.v:469-475), so the contract names neither.
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load4 of n_kept at c + 0x23ac (shadow test 0x87808-0x87818, slow path 0x878cc, error arm
     __asan_report_load4 at 0x878dc); check 2, the same word re-read for n_kept++ (shadow test 0x87874-0x87878,
     slow path 0x878f0, error arm at 0x87900); check 3, load4 of refused at c + 0x2008 (0x87888-0x8789c, slow path
     0x878e0, error arm at 0x878ec). In image A the two stores reuse their load's check (the row counts _load4:3
     only); image B gives the n_kept store its own check (at 0x87934, found by the plain / UBSan owner's review),
     so the contract does not rely on either layout: every load and every store of n_kept and refused, checked or
     not, is killed by m_refuse_pre's sa_addr rd c SEG_M_SIZE.
   - snprintf's ranges: the destination kept[n_kept] (112 bytes) and the %s argument c->reading (its bytes and
     NUL) lie in the block: the same sa_addr; the reading's slack past the block's end: sa_tail rd
     (c + SEG_M_SIZE - 1), the plain blk_slack (c is 16-aligned, so it names exactly the 4 bytes
     [c + 9236, c + 9240)); the format literal: sa_lit (string with slack, addressable, 0 < address, an image
     object) through the parameter lit, M_REFUSE_LITS below.
   - where the block lies: sa_heap (calloc(1, 0x2414) at LLVMFuzzerTestOneInput 0x84f94, PREMISES-A.md section
     2.3), in place of the plain blk_noimg / wr_at, never by an address bound against the image's end; sa_heap and
     sa_addr give sa_dst's heap arm for every byte it writes. The real stack window [sp - STK, sp) is apart from a
     heap block, so the plain apart premise is not restated.
   - printf: sa_frm0 and sa_ssp rd gotw guard (the plain printf_env's frm0 and stack-protector cells), gotw guard
     parameters; the post is apost_baseF (printf_core writes fa0 and may set the rounding mode to 0).
   - arodata_okP over the read-only window RLO RHI, a contract parameter (each image's walk gives its RELRO
     bounds): the released printf texts ask the image's read-only view, which AR does not give.
   - counters: refused is u32 (seg_spec.u32_enc in mconf_encp; mc_refused mc + 1 < 2 ^ 32 keeps the + 1 exact);
     line is the int argument of %d, 0 <= line <= 65536 < 2 ^ 31.
   - no side-stack frame: EV_m_refuse = 0, post tail sa_kept and sa_noalloc.
   - sa_kept over the ranges of m_refuse_W: its own stores are n_kept and refused (sw 0x87884, 0x878a8); the
     released snprintf post keeps every byte outside [d, d + sn_len (n - 1) T) and its K-byte scratch window
     (fuzz_command lib/A/Rt/RtPFCmd.v:341-342 and RtPFShared.v:187-188 at 501c0d516c69), with d = kept[n_kept]
     and sn_len (n - 1) T <= n = 112; no set_shadow entry, no side-stack frame. The K window lies in
     [sp - STK_m_refuse, sp) when STK_m_refuse >= 48 + K.
   Call sites (segA/evidence/callsites.asan.tsv lines 96, 99, 101, 105, 117, 119, 120, 123, 15, 16): m_file
   0x861ec, 0x863ac, 0x8653c, 0x867a8, 0x86b14, 0x86bd4, 0x86bf4, 0x86ccc (a0 = c, a1 = the line number, in
   [1, 65536]; knock = true only when 0x86ccc is reached from the knock branch, ieq S_knock at 0x86b30, with the
   store at 0x86b84 or, n_kept = 8, without it (mconf_encp's pending flag is then vacuous); false elsewhere);
   LLVMFuzzerTestOneInput 0x852bc (a1 = 0) and 0x852ec (knock = false).
   image A: A_m_refuse = 0x877d0; lit F_addr_line = 0x210c0 (.str.6), lit F_addr = 0x210e0 (.str.7) (nm lines
   1032-1033; their text read from the pin's LOAD bytes by this lane, INFERENCE grade by the brief's rule, and
   the plain contract's formats at the same two calls); STK_m_refuse = 48 + the window row 4's snprintf text asks
   (INFERENCE; the plain M_REFUSE_STACK = 16 + PRINTF_K is the plain build's).
   IMAGE-INDEPENDENT: no image module is Required; A_m_refuse, STK_m_refuse, RLO, RHI, lit, gotw and guard are
   parameters.
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626), row 4):
     RtPFSeg.seg_asnprintf_realizes (img_lo img_hi cr pc gotw guard) over the extended piece grammar (row 4,
     commit 755e9278f8ff, RtPFSeg.v:228), at the snprintf trampoline (image A 0x43a64,
     interceptor 0x49054), for both formats.
   They are NOT premises of this contract: the statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/m_refuse_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* the .rodata literals m_refuse hands to snprintf: its two formats (image A .str.6 0x210c0, .str.7 0x210e0) *)
Definition M_REFUSE_LITS : list (list Z) := [SegModel.F_addr_line; SegModel.F_addr].
(* The bytes it writes outside its own stack window (the plain m_refuse_W, lib/Prog/m_refuse_c.v:59-65, without
   its first range (sp - M_REFUSE_STACK, sp), the stack window): kept[n_kept] and n_kept when n_kept < 8, refused. *)
Definition m_refuse_W (c : Z) (mc : mconf) : list (Z * Z) :=
(if Z.of_nat (length (mc_kept mc)) <? 8 then
   [(seg_spec.kept_addr c (length (mc_kept mc)), seg_spec.kept_addr c (length (mc_kept mc)) + seg_spec.MC_KEPT_LEN);
    (c + seg_spec.MC_NKEPT, c + seg_spec.MC_NKEPT + 4)]
 else []) ++
[(c + seg_spec.MC_REFUSED, c + seg_spec.MC_REFUSED + 4)].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* The plain m_refuse_pre (lib/Prog/m_refuse_c.v:50-56) over the reader rd = aview segs (w_H W) mem: c the mconf
   block, nonzero, 16-aligned, a live heap block of 9236 bytes, addressable, holding mc with the pending knock
   flag knock, and the slack after its end mapped (blk_slack); the line and refused bounds; printf's machine and
   stack-protector facts; the formats, through lit. The plain blk_noimg / wr_at / apart / stack_ok / mem_inv
   conjuncts are afn_pre's and sa_heap's here. Outside the sections:
   m_refuse_pre segs B ly S rd lit gotw guard c line mc knock. *)
Definition m_refuse_pre (ly : alayout) (S : astate) (rd : reader) (lit : list Z -> Z) (gotw guard c line : Z)
(mc : mconf) (knock : bool) : Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_heap B ly S c seg_spec.SEG_M_SIZE /\ sa_addr rd c seg_spec.SEG_M_SIZE /\
sa_mconfp knock rd c mc /\ sa_tail rd (c + seg_spec.SEG_M_SIZE - 1) /\
0 <= line <= 65536 /\ mc_refused mc + 1 < 2 ^ 32 /\
sa_frm0 /\ sa_ssp rd gotw guard /\
(forall x, In x M_REFUSE_LITS -> sa_lit segs B rd (lit x) x).
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_m_refuse : Z := 0.
Definition m_refuse_contract (A_m_refuse STK_m_refuse RLO RHI : Z) (lit : list Z -> Z) (gotw guard : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c line : Z) (mc : mconf) (knock : bool),
afn_pre segs B STK_m_refuse ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 line ->
m_refuse_pre ly S (aview segs (w_H W) mem) lit gotw guard c line mc knock ->
st_nev S + EV_m_refuse <= EV_MAX ->
SRr segs W (cfg_at segs A_m_refuse regs mem md)
(apost_baseF segs B STK_m_refuse (m_refuse_W c mc) regs ly S W mem md EV_m_refuse
(fun ly' S' W' regs' mem' md' =>
 sa_mconf (aview segs (w_H W') mem') c (SegModel.m_refuse mc line knock) /\
 sa_kept segs W mem W' mem' regs STK_m_refuse
 (fun a =>
  (Z.of_nat (length (mc_kept mc)) < 8 /\
   seg_spec.kept_addr c (length (mc_kept mc)) <= a <
   seg_spec.kept_addr c (length (mc_kept mc)) + seg_spec.MC_KEPT_LEN) \/
  (Z.of_nat (length (mc_kept mc)) < 8 /\ c + seg_spec.MC_NKEPT <= a < c + seg_spec.MC_NKEPT + 4) \/
  c + seg_spec.MC_REFUSED <= a < c + seg_spec.MC_REFUSED + 4) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
