(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7x.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Reusable/YC7x.v, with its module paths and module names changed; 39 of its 59 lines of code are new or changed and 147 lines of the source are left out. *)
(* check_provenance (fuzz_segconf.c:485-500; fuzz_segconf.asan 0x872e0, 232 bytes, 58 instructions; frame 32
   bytes): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return). Functional content: the plain contract
   lib/Prog/check_provenance_c.v:10-47 (check_provenance_pre :27-34), restated over the ASan reader
   rd = aview segs (w_H W) mem.
   !same_text(role_file, want->role_set ? want->role_file : NULL), or the same for ignore_file, aborts, each as in
   check_model. The code reads want->role_set (want + 0x14, `lw`), forms want + 0x3c or 0, returns to the second
   test when rf (a0) equals it (0x87330), else aborts when rf = 0 (0x87334) or role_set = 0 (0x87338), else calls
   strcmp(rf, want + 0x3c) (0x8733c) and aborts on a nonzero result (0x87340); then the same with want->ignore_set
   (want + 0x1c), igf (a1, kept in s0) and want + 0x9c: 0x8736c, 0x87370, 0x87374, strcmp 0x8737c, 0x87380. It
   writes only its frame.
   The abort site 0x873a0 (after __asan_handle_no_return 0x8739c) is reached from 0x87334, 0x87338, 0x87340,
   0x87370, 0x87374 and 0x87380; all six are dead under check_seg's last two conjuncts, the two same_text
   conjuncts of check_provenance_pre, by check_model's argument for each pair (o = None: pointer 0 and flag 0;
   o = Some s: pointer nonzero, flag 1, s equal to the field, so the strcmp row's post gives a zero result).
   Post: the plain post is ret_void's `fun _ => True` with munch [(sp - 32, sp)]; here apost_base with footprint []
   (the frame is inside the call's own window [sp - STK_check_provenance, sp)) and the post tail
   sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract:
   - sa_addr rd want MSEG_SIZE kills both load4 check sites, want + 0x14 (shadow byte `lb` 0x87314, error arm
     __asan_report_load4 0x873b4) and want + 0x1c (shadow byte 0x87350, error arm 0x873c4), and gives strcmp's
     ranges of the fields at want + 0x3c and want + 0x9c.
   - sa_addr rd rf (length + 1) and sa_addr rd igf (length + 1) give strcmp's ranges of the two arguments.
   - the two arguments' tails: the strcmp row asks atail_vis of both strings, so rf and igf are stated with
     sa_ostr (sa_strz plus sa_tail) where the plain contract had ocstrz_at; the fields' tails lie inside the mseg
     entry, whose 256 bytes sa_mseg fixes (cstr_enc 96 at 0x3c and at 0x9c end by 0x9c and 0xfc).
   - length + 1 < 2 ^ 32 for each argument: the row's range check, aread_ok, asks it (fuzz_command
     lib/A/Rt/RtDefs.v:35-36 at 501c0d516c69); sa_addr bounds it only by 2 ^ 63.
   - sa_heap of want (in m = calloc(1, 0x2414)) and of each argument (seg_spec.role_file_ptr / ignore_file_ptr,
     fields of the reader's block c = malloc(0x40e8); PREMISES-A section 2.3) in place of the plain
     `apart _ _ lo sp`: a live heap block lies outside the stack window and outside the interceptor's scratch.
   - arodata_okP segs RLO RHI B rd (RLO RHI the read-only window, contract parameters: each image's walk passes
     its own RELRO bounds): the strcmp row asks rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which AR does
     not give.
   - The shadow base is read through the GOT word 0xa2a50 and __asan_shadow_memory_dynamic_address 0xabff8
     (0x872fc-0x87304; PREMISES-A section 1.5): AR's const cells as_got_shadow / as_shadow_cell
     (lib/Reusable/YG0f.v aso_const_law), so neither is a premise or a parameter.
   - No side-stack frame, no printf, no allocator entry: EV_check_provenance = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_provenance (fun _ => False): every byte outside the window
     [sp - STK_check_provenance, sp) reads at the exit as at the entry, the shadow of image objects included,
     which the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow
     entry, its own stores are into its frame (`sd` 0x872e4-0x872f0), and the strcmp row's post keeps every byte
     outside the interceptor's scratch window with E = False (art_post, fuzz_command lib/A/Rt/RtDefs.v:89-99;
     RtString.v astrcmp_realizes), a window STK_check_provenance covers, at both calls; the abort and report
     arms are dead.
   IMAGE-INDEPENDENT: no image module is Required; A_check_provenance, STK_check_provenance, RLO and RHI are
   parameters (image A: A_check_provenance = 0x872e0; STK_check_provenance covers the 32-byte frame and the window
   the strcmp row asks).
   Call site: LLVMFuzzerTestOneInput 0x85568 (segA/evidence/callsites.asan.tsv).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); rows 16-19 were added by the
   accepted v1, 5e0b8a44fdc):
     RtString.astrcmp_realizes (row 17) at the strcmp trampoline (image A 0x43a14), for both calls.
   It is NOT a premise of this contract: the statement does not mention it. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Prog/check_provenance_c.v, derived mechanically (bkit derive_b.py): its Require lines name the lib/B copies; nothing else differs. The comments are the A file's. *)
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
Definition EV_check_provenance : Z := 0.
(* the plain check_provenance_pre over the reader: the mseg entry want and the strings rf and igf (where each
   lies, its shadow and the arguments' tails added), and check_seg's last two conjuncts *)
Definition check_provenance_pre (ly : alayout) (S : astate) (rd : reader) (rf igf want : Z)
(orf oif : option (list Z)) (g : mseg) : Prop :=
want mod 4 = 0 /\ sa_mseg rd want g /\ sa_heap B ly S want seg_spec.MSEG_SIZE /\
sa_addr rd want seg_spec.MSEG_SIZE /\
sa_ostr rd rf orf /\
(match orf with
 | Some s => Z.of_nat (length s) + 1 < 2 ^ 32 /\ sa_heap B ly S rf (Z.of_nat (length s) + 1) /\
             sa_addr rd rf (Z.of_nat (length s) + 1)
 | None => True
 end) /\
sa_ostr rd igf oif /\
(match oif with
 | Some s => Z.of_nat (length s) + 1 < 2 ^ 32 /\ sa_heap B ly S igf (Z.of_nat (length s) + 1) /\
             sa_addr rd igf (Z.of_nat (length s) + 1)
 | None => True
 end) /\
same_text orf (if ms_role_set g then Some (ms_role_file g) else None) = true /\
same_text oif (if ms_ignore_set g then Some (ms_ignore_file g) else None) = true.
Definition check_provenance_contract (A_check_provenance STK_check_provenance RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (rf igf want : Z) (orf oif : option (list Z)) (g : mseg),
afn_pre segs B STK_check_provenance ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 rf -> 0 <= rf < 2 ^ 64 ->
getr regs 11 = w64 igf -> 0 <= igf < 2 ^ 64 ->
getr regs 12 = w64 want -> 0 <= want < 2 ^ 64 ->
check_provenance_pre ly S (aview segs (w_H W) mem) rf igf want orf oif g ->
st_nev S + EV_check_provenance <= EV_MAX ->
SRr segs W (cfg_at segs A_check_provenance regs mem md)
(apost_base segs B STK_check_provenance [] regs ly S W mem md EV_check_provenance
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_provenance (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
