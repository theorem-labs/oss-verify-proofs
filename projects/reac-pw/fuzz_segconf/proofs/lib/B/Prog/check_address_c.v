(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 28 of its 48 lines of code are new or changed and 147 lines of the source are left out. *)
(* check_address (fuzz_segconf.c:531-542; fuzz_segconf.asan 0x874b8, 80 bytes, 20 instructions; frame 32 bytes):
   the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr
   of apost_base at the return). Functional content: the plain contract lib/Prog/check_address_c.v:10-44
   (check_address_pre :27-31), restated over the ASan reader rd = aview segs (w_H W) mem.
   n = strlen(want) (0x874d4); strncmp(got, want, n) <> 0 aborts (0x874e4, tested at 0x874e8). It has no inline
   check of its own and writes only its frame.
   The abort site 0x87504 (after __asan_handle_no_return 0x87500) is reached from 0x874e8 only; it is dead under
   check_kept's first conjunct, SegModel.strncmp gs ws (SegModel.strlen ws) = 0: the strlen row returns
   length ws, and the strncmp row's post is the zero result exactly when StrFun.strncmp_model gives 0, which agrees
   with SegModel.strncmp on these strings (the plain contract's Spec/SegBridge.v).
   Post: the plain post is ret_void's `fun _ => True` with munch [(sp - 32, sp)]; here apost_base with footprint []
   (the frame is inside the call's own window [sp - STK_check_address, sp)) and the post tail
   sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract (no inline check site: the row of program.asan.tsv counts 0):
   - sa_addr rd want (length ws + 1): the strlen row's range and the strncmp row's range of want (it reads
     min n (length ws + 1) bytes, n = length ws).
   - sa_addr rd got (length gs + 1): the strncmp row's range of got (min n (length gs + 1) bytes).
   - amem_range got (length gs + 8) and amem_range want (length ws + 8): the strncmp row asks 8 bytes of band
     room past each string (fuzz_command lib/A/Rt/RtString.v:121-137 at 501c0d516c69).
   - got's tail: the strncmp row asks atail_vis of both strings, so got is stated with sa_str (sa_strz plus
     sa_tail) where the plain contract had cstrz_at; want had its slack already (cstr_at), here sa_str.
   - length + 1 < 2 ^ 32 for both strings: the rows' range check, aread_ok, asks it (fuzz_command
     lib/A/Rt/RtDefs.v:35-36 at 501c0d516c69), and the strncmp row asks 0 <= n < 2 ^ 32 of n = length ws; sa_addr
     bounds a length only by 2 ^ 63. (Both strings are fields of fixed size, c->refusal[i] char[200] and
     m->kept[i] char[112], so the caller has it from the encodings.)
   - sa_heap of both strings in place of the plain `apart _ _ lo sp`: got = c + 0x2e88 + 200 i lies in the reader's
     block c = malloc(0x40e8) and want = m + 0x200c + 112 i in m = calloc(1, 0x2414) (PREMISES-A section 2.3);
     a live heap block lies outside the stack window and outside the interceptors' scratch.
   - arodata_okP segs RLO RHI B rd (RLO RHI the read-only window, contract parameters: each image's walk passes its
     own RELRO bounds): the strlen and strncmp rows ask rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which
     AR does not give.
   - No side-stack frame, no printf, no allocator entry: EV_check_address = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_address (fun _ => False): every byte outside the window
     [sp - STK_check_address, sp) reads at the exit as at the entry, the shadow of image objects included, which
     the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow entry,
     its own stores are into its frame (`sd` 0x874bc-0x874c4), and the strlen and strncmp rows' posts keep every
     byte outside the interceptor's scratch window with E = False (art_post, fuzz_command lib/A/Rt/RtDefs.v:89-99;
     RtString.v astrlen_realizes, astrncmp_realizes), windows STK_check_address covers; the abort arm is dead.
   IMAGE-INDEPENDENT: no image module is Required; A_check_address, STK_check_address, RLO and RHI are parameters
   (image A: A_check_address = 0x874b8; STK_check_address covers the 32-byte frame and the deeper of the windows
   the strlen and strncmp rows ask).
   Call site: LLVMFuzzerTestOneInput 0x85648 (segA/evidence/callsites.asan.tsv).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); rows 16-19 were added by the
   accepted v1, 5e0b8a44fdc):
     RtString.astrlen_realizes (row 16) at the strlen trampoline (image A 0x43a0c),
     RtString.astrncmp_realizes (row 1) at the strncmp trampoline (image A 0x43a18).
   They are NOT premises of this contract: the statement does not mention them. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_address_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_check_address : Z := 0.
(* the plain check_address_pre over the reader: the two strings (where each lies, its shadow, its tail, its
   length bound and its band room added) and check_kept's first conjunct *)
Definition check_address_pre (ly : alayout) (S : astate) (rd : reader) (got want : Z) (gs ws : list Z) : Prop :=
got <> 0 /\ sa_str rd got gs /\ Z.of_nat (length gs) + 1 < 2 ^ 32 /\
sa_heap B ly S got (Z.of_nat (length gs) + 1) /\ sa_addr rd got (Z.of_nat (length gs) + 1) /\
amem_range got (Z.of_nat (length gs) + 8) /\
want <> 0 /\ sa_str rd want ws /\ Z.of_nat (length ws) + 1 < 2 ^ 32 /\
sa_heap B ly S want (Z.of_nat (length ws) + 1) /\ sa_addr rd want (Z.of_nat (length ws) + 1) /\
amem_range want (Z.of_nat (length ws) + 8) /\
SegModel.strncmp gs ws (SegModel.strlen ws) = 0.
Definition check_address_contract (A_check_address STK_check_address RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (got want : Z) (gs ws : list Z),
afn_pre segs B STK_check_address ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 got -> 0 <= got < 2 ^ 64 ->
getr regs 11 = w64 want -> 0 <= want < 2 ^ 64 ->
check_address_pre ly S (aview segs (w_H W) mem) got want gs ws ->
st_nev S + EV_check_address <= EV_MAX ->
SRr segs W (cfg_at segs A_check_address regs mem md)
(apost_base segs B STK_check_address [] regs ly S W mem md EV_check_address
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_address (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
