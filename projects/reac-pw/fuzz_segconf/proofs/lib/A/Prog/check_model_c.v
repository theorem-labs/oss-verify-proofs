(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC7z.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC7z.v, with its module paths and module names changed; 18 of its 41 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/reac_segconf_ignore_file_c.v; 22 of its 50 lines of code are new or changed and 13 lines of the source are left out. *)
(* check_model (fuzz_segconf.c:457-468; fuzz_segconf.asan 0x87210, 120 bytes, 30 instructions; frame 16 bytes): the
   contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the entry, SRr of
   apost_base at the return). Functional content: the plain contract lib/Prog/check_model_c.v:10-43
   (check_model_pre :26-30), restated over the ASan reader rd = aview segs (w_H W) mem.
   !same_text(got, want->model_set ? want->model : NULL) aborts. The code reads want->model_set (want + 0x20,
   `lw`), forms want_p = model_set ? want + 0x24 : 0 (seqz / addi / and, 0x8723c-0x87248) and returns when
   got (a0) = want_p (0x8724c); else it aborts when got = 0 (0x87250) or model_set = 0 (0x87254), else calls
   strcmp(got, want + 0x24) (0x87258) and aborts when the result is nonzero (0x8725c). It writes only its frame.
   The abort site 0x87270 (after __asan_handle_no_return 0x8726c) is reached from 0x87250, 0x87254 and 0x8725c; all
   three are dead under check_seg's second conjunct, same_text o (if ms_model_set g then Some (ms_model g) else
   None) = true: o = None makes got = 0 and asks model_set = 0, so got = want_p = 0; o = Some s makes got <> 0 and
   asks model_set = 1 and s = ms_model g, so the strcmp row's post gives a zero result.
   Post: the plain post is ret_void's `fun _ => True` with munch [(sp - 16, sp)]; here apost_base with footprint []
   (the frame is inside the call's own window [sp - STK_check_model, sp)) and the post tail
   sa_kept /\ sa_noalloc.
   ASAN FACTS ADDED over the plain contract:
   - sa_addr rd want MSEG_SIZE kills the one load4 check site, want + 0x20 (shadow byte `lb` 0x87230, error arm
     __asan_report_load4 0x87284), and gives strcmp's range of the model field [want + 0x24, length + 1).
   - sa_addr rd got (length s + 1) gives strcmp's range of got.
   - got's tail: the strcmp row asks atail_vis of both strings, so got is stated with sa_ostr (sa_strz plus
     sa_tail) where the plain contract had ocstrz_at; the model field's tail lies inside the mseg entry, whose 256
     bytes sa_mseg fixes (cstr_enc 24 at 0x24 ends by 0x3c).
   - length s + 1 < 2 ^ 32: the row's range check, aread_ok, asks its length below 2 ^ 32 (fuzz_command
     lib/A/Rt/RtDefs.v:35-36 at 501c0d516c69); sa_addr bounds it only by 2 ^ 63.
   - sa_heap of want (in m = calloc(1, 0x2414)) and of got (seg_spec.model_ptr, a field of the reader's block
     c = malloc(0x40e8); PREMISES-A section 2.3) in place of the plain `apart _ _ lo sp`: a live heap block lies
     outside the stack window and outside the interceptor's scratch.
   - arodata_okP segs RLO RHI B rd (RLO RHI the read-only window, contract parameters: each image's walk passes
     its own RELRO bounds): the strcmp row asks rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which AR does
     not give.
   - The shadow base is read through the GOT word 0xa2a50 and __asan_shadow_memory_dynamic_address 0xabff8
     (0x87218-0x87220; PREMISES-A section 1.5): AR's const cells as_got_shadow / as_shadow_cell
     (lib/Reusable/YG0f.v aso_const_law), so neither is a premise or a parameter.
   - No side-stack frame, no printf, no allocator entry: EV_check_model = 0, apost_base, sa_noalloc.
   - sa_kept segs W mem W' mem' regs STK_check_model (fun _ => False): every byte outside the window
     [sp - STK_check_model, sp) reads at the exit as at the entry, the shadow of image objects included, which
     the journal does not keep (SegABase.v, sa_kept). True of the code: no side-stack frame, no set_shadow entry,
     its one store is into its frame (`sd ra,8(sp)` 0x87214), and the strcmp row's post keeps every byte
     outside the interceptor's scratch window with E = False (art_post, fuzz_command lib/A/Rt/RtDefs.v:89-99;
     RtString.v astrcmp_realizes), a window STK_check_model covers; the abort and report arms are dead.
   IMAGE-INDEPENDENT: no image module is Required; A_check_model, STK_check_model, RLO and RHI are parameters
   (image A: A_check_model = 0x87210; STK_check_model covers the 16-byte frame and the window the strcmp row asks).
   Call site: LLVMFuzzerTestOneInput 0x85528 (provenance/evidence/image-tables/callsites.asan.tsv).
   The WALK takes these runtime entries as Section hypotheses (the interceptor lane's interface
   provenance/evidence/interceptors/INTERFACE-A-interceptors.md (commit 7068323e2626); rows 16-19 were added by the
   accepted v1, 5e0b8a44fdc):
     RtString.astrcmp_realizes (row 17) at the strcmp trampoline (image A 0x43a14).
   It is NOT a premise of this contract: the statement does not mention it. *)
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
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_check_model : Z := 0.
(* the plain check_model_pre over the reader: the mseg entry want and the string got (where each lies, its shadow
   and got's tail added), and check_seg's second conjunct *)
Definition check_model_pre (ly : alayout) (S : astate) (rd : reader) (got want : Z) (o : option (list Z))
(g : mseg) : Prop :=
want mod 4 = 0 /\ sa_mseg rd want g /\ sa_heap B ly S want seg_spec.MSEG_SIZE /\
sa_addr rd want seg_spec.MSEG_SIZE /\
sa_ostr rd got o /\
(match o with
 | Some s => Z.of_nat (length s) + 1 < 2 ^ 32 /\ sa_heap B ly S got (Z.of_nat (length s) + 1) /\
             sa_addr rd got (Z.of_nat (length s) + 1)
 | None => True
 end) /\
same_text o (if ms_model_set g then Some (ms_model g) else None) = true.
Definition check_model_contract (A_check_model STK_check_model RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (got want : Z) (o : option (list Z)) (g : mseg),
afn_pre segs B STK_check_model ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 got -> 0 <= got < 2 ^ 64 ->
getr regs 11 = w64 want -> 0 <= want < 2 ^ 64 ->
check_model_pre ly S (aview segs (w_H W) mem) got want o g ->
st_nev S + EV_check_model <= EV_MAX ->
SRr segs W (cfg_at segs A_check_model regs mem md)
(apost_base segs B STK_check_model [] regs ly S W mem md EV_check_model
(fun ly' S' W' regs' mem' md' =>
 sa_kept segs W mem W' mem' regs STK_check_model (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
