(* trim (reac_segconf.c:50-59, static; fuzz_segconf.asan 0x890a8, 296 bytes, 74 instructions; frame 32 bytes,
   no side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form
   (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/trim_c.v:10-48 (trim_pre :29-31, trim_end_addr :33-34,
   the contract :36-48), restated over the ASan reader.
   What the code does (objdump of fuzz_segconf.asan, 0x890a8-0x891cc): past the leading blanks (the byte loop at
   0x890e0, `bltu 0x20, c` then the bit mask 0x100002200), e = s + strlen(s) (jal 0x89124 to the strlen
   trampoline), back over the trailing blanks while e > s (0x89148), `sb zero,0(e)` (0x891a0), return s. The post
   is the plain one: a0 = p + seg_spec.trim_lead s, and the bytes at p are the first trim_lead s + length (r_trim s)
   bytes of s, then a NUL.
   What it reads: the shadow base through the GOT word as_got_shadow B (image A 0xa2a50, which holds 0xabff8 =
   as_shadow_cell B; AR's constants, lib/Reusable/YG0d.v AR_const_law), so the contract names neither; the string
   at p with its slack. What it writes: its frame and the one NUL byte at trim_end_addr p s, so its footprint is
   that byte. No abort site (provenance/evidence/image-tables/program.asan.tsv line 21).
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load1 of a leading byte (shadow test 0x890e0-0x89114, error arm __asan_report_load1 at
     0x8911c), inline check 2, load1 of a trailing byte e[-1] (0x89148-0x89184, error arm 0x89188), inline check 3,
     store1 of the NUL at e (0x89190-0x891c4, error arm __asan_report_store1 at 0x891cc): every address lies in
     [p, p + length s + 1), killed by trim_pre's sa_addr rd p (length s + 1).
   - strlen's range check on [p + lead, p + length s + 1): the same sa_addr; its musl word loop reads the slack
     after the NUL: sa_str (not sa_strz). The interceptor's range is below 2 ^ 32 (aread_ok): the last conjunct.
   - where the string lies: sa_dst over [p, p + length s + 1) (the plain wr_at and apart from [lo, sp)): a live
     side-stack frame (parse_file's class-5 frame holds buf, the only object any call site passes: its object
     description `buf:142` at frame offset 64, 512 bytes, .rodata 0x17667), a heap block, or the caller's real
     stack above this sp (parse_file's real-stack fallback, dead under the pinned use-after-return flag).
   - arodata_okP over the window RLO .. RHI: row 16's RtString.astrlen_realizes asks rt_rom_view (fuzz_command
     lib/A/Rt/RtDefs.v:145 at origin/ossv/recipes 501c0d516c69), which AR does not give.
   - no side-stack frame and no printf: apost_base, EV_trim = 0, post tail sa_noalloc.
   - the keep clause sa_kept (SegABase.v; fuzz_command's art_post keep clause, lib/A/Rt/RtDefs.v): every byte
     outside this call's stack window and the NUL byte is unchanged, the shadow included (apost_base's journal
     keeps no shadow of an image object, so a caller could not carry a literal's sa_addr across the call
     without it). True of the code: trim takes no side-stack frame, and row 16's post keeps every byte outside
     its ESTACK window (fuzz_command RtString.v astrlen_realizes, POST with E = False), which lies in STK_trim.
   Call sites (provenance/evidence/image-tables/callsites.asan.tsv lines 238, 241, 242, 246, 253): reac_segconf_parse_file 0x87f44
   (trim(buf)), 0x87fdc (trim(line) after `*eq = 0`), 0x87fe8 (trim(eq + 1)), 0x880c4 (trim(line + 1) after
   `*close = 0`), 0x88310 (trim(body + 7)); every argument points into parse_file's buf[512], at a C string of at
   most 511 bytes.
   image A: A_trim = 0x890a8; STK_trim = 32 + ESTACK (INFERENCE: its frame and the ESTACK window row 16 asks below
   it); RLO = 0xa14a0 (.data.rel.ro), RHI = 0xa3748 (PT_GNU_RELRO 0xa1468 + file size 0x22e0), both from
   fuzz_segconf.asan's section and program headers (pin 48c5355bdacb), fuzz_command's CmdGlob.v convention.
   IMAGE-INDEPENDENT: no image module is Required; A_trim, STK_trim, RLO and RHI are parameters.
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); row 16 is in the accepted v1,
   5e0b8a44fdc; at e45889d6935a strlen is that file's DECISION 2, option (b)):
     RtString.astrlen_realizes (row 16), at the strlen trampoline (image A 0x43a0c, interceptor 0x43abc).
   They are NOT premises of this contract: the statement does not mention them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* Where trim stores the NUL (the plain trim_end_addr, lib/Prog/trim_c.v:34). *)
Definition trim_end_addr (p : Z) (s : list Z) : Z :=
p + Z.of_nat (seg_spec.trim_lead s + length (SegModel.r_trim s)).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* What trim asks of its caller (the plain trim_pre, lib/Prog/trim_c.v:29-31, over the reader
   aview segs (w_H W) mem): p is the C string s with its slack, its bytes and NUL addressable and a destination
   this call may write (a live side-stack frame, a heap block, or the caller's real stack above sp), and short
   enough for the interceptor's range. The plain stack_ok / apart / mem_inv conjuncts are afn_pre's and sa_dst's
   here. Outside the sections: trim_pre segs B ly S W mem regs p s. *)
Definition trim_pre (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
(regs : bvmap 5 word) (p : Z) (s : list Z) : Prop :=
p <> 0 /\ sa_str (aview segs (w_H W) mem) p s /\
sa_addr (aview segs (w_H W) mem) p (Z.of_nat (length s) + 1) /\
sa_dst segs B ly S W mem regs p (Z.of_nat (length s) + 1) /\ Z.of_nat (length s) + 1 < 2 ^ 32.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_trim : Z := 0.
Definition trim_contract (A_trim STK_trim RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p : Z) (s : list Z),
afn_pre segs B STK_trim ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 p -> 0 <= p < 2 ^ 64 ->
trim_pre ly S W mem regs p s ->
st_nev S + EV_trim <= EV_MAX ->
SRr segs W (cfg_at segs A_trim regs mem md)
(apost_base segs B STK_trim [(trim_end_addr p s, trim_end_addr p s + 1)] regs ly S W mem md EV_trim
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (p + Z.of_nat (seg_spec.trim_lead s)) /\
 sa_bytes (aview segs (w_H W') mem') p
   (seg_spec.zb (firstn (seg_spec.trim_lead s + length (SegModel.r_trim s)) s) ++ [seg_spec.ZERO]) /\
 sa_kept segs W mem W' mem' regs STK_trim (fun a => a = trim_end_addr p s) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
