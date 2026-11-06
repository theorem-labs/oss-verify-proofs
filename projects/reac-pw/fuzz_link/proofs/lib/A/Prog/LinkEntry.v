(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfn.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_pcap on libreac v1.9.0, ASan build (image root: the original v1.9.0 pins, (internal path), sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin x/unstripped/fuzz_pcap/fuzz_pcap.asan; capstone disassembly); module paths changed. Relocated constants (the image's own, A_LLVMF / RA_LLVMF / A_EMPTY / LLVMF_STK / G_HARNESS, with their measurements, are in lib/A/Prog/PcapEntryA.v): EV_LIB = 10 (allocator events of the worst path, each a malloc, free or free(NULL): malloc 0x80940, the malloc of musl fmemopen 0x8e908 under pcap_source_open 0x8099c, malloc 0x80ab8, fclose's free(NULL) 0x8e2b4 and free 0x8e2bc under pcap_source_close 0x810a8, malloc 0x8e908 under pcap_source_open 0x810c4, the two frees of fclose under pcap_source_close 0x810e8, free 0x8110c, free 0x81114; a refused file makes 5 and an abort path at most 8; pcap_source_next and the side-stack calls make none); LIVE_LIB = 2^26 + 1304 + 2040 (the bytes the call may hold at once beyond its caller's: the copy of the file, size - 1 <= 2^26 - 2 bytes (0x80914, malloc 0x80940), one 1304-byte FILE block (musl fmemopen 0x8e904 `addi a0,zero,0x518`; close #1 frees it before the reopen allocates the next), the record buffer max(cap, 1) <= 2040 bytes (0x80aa8 `slli s5,a1,3` of one input byte, 0x80ab4)). The library shape is fuzz_pcap's agreement shape AgreePcap.ag_out_shape (lib/AgreePcap.v:26, the shape of the released plain entry contract and of lib/A/PcapAsanTop.v's pcap_shape) in place of cgif's Context lib_shape, written as its LIBK's own shape, the plain lib/OutForm.v's out_shape PWalk.OUT (ag_out_shape = AgreeShape.ag_shape (out_shape PWalk.OUT) and AgreeShape.ag_LIBK is reflexivity, so the two LIBK terms are convertible): AgreePcap and AgreeShape are not Required here because they load every image module. cgif's write sink (asink_none) is replaced by fuzz_pcap's read-stream state asource_none (lib/A/Stdio/PSource.v) over a Section variable KS : asource_syms, with the premise as_ofl_head KS = AOFL_HEAD that the fmemopen wrapper's statement asks; the image segments are fuzz_pcap's Asan.M.loaded_segments; the meta-region invariant is the source-side asrc_meta_inv segs KS (lib/A/Stdio/PSourceMeta.v, body identical to cgif's ameta_inv with ak_ -> as_), so cgif's sink record tfib_K is gone and tfib_lib_contract_x_all takes KS (and the sink head {SK}) beyond ACfn.v's arguments; the donor's fd-names conjunct of asink_none (YE00.v:124, fd_names_path (m_fds md) sink_path = false) is carried as the INERT fd-names invariant on the pre and the post (cgif's sink path stays a literal; pcap never opens it), since fuzz_pcap opens no descriptor by name (libreac_fuzz_fopen's callees are the strcmp wrapper 0x80760 and the fmemopen wrapper, tail jump 0x807ac; its fopen tail jump 0x80780 is reached only by 0x80750 (path NULL) or 0x80764 (strcmp nonzero), both refuted by its premises: the path is the literal 0x20d00 and the string is equal); SK is a Section variable, EXPLICIT on every exported statement (Arguments below: the only global sink_head instance in this closure is the plain build's, so it must never be inferred), and no branch defines fuzz_pcap's relocated AB1v / AE2k. The post's output is cgif's ll_out l = [] restated as ll_out l = PWalk.OUT pl (lib/Prog/Slot/PWalk.v:205), the output the agreement shape's LIBK hands its continuation (LIBK pl fs K = wr ch_stderr (OUT pl) (K (LL 0 fs (OUT pl)))), so tfib_lib_post_x takes pl after n; PcapEntryDefs.v proves PWalk.OUT pl = [] (pcap_OUT_nil: v1.9.0's reader prints nothing), which a walk uses to meet it. IMAGE-GENERIC (a Theorem Labs lane ruling): the contract text is one for both images; every image datum it names is a Section variable (segs, the read-only window rlo / rhi, a_llvmf, ra_llvmf, a_empty, and the stack bound stk, a composition over the image's own frames), and the harness's global ranges G); lib/A's values and the lib/A instance tfib_lib_contract_x_all_A (segs := Asan.M.loaded_segments, rlo / rhi := PcapRelro.PCAP_RLO / PCAP_RHI, G := G_HARNESS = [(0x5d3f40, 8); (0x5d3f60, 8)]) are in lib/A/Prog/PcapEntryA.v. HARNESS GLOBALS (a Theorem Labs lane decision): the post's journal is W_journal.v's ajournal_gx segs B G 0 [] (the donor's ajournal relative to a start memory that agrees with the true one outside G; XO = 0 and OUT = [], no out-parameter), because the harness writes g_file / g_file_len, which are not in as_owned_static. EV_LIB and LIVE_LIB stay shared constants: the allocator calls and their sizes are the same in both builds (internal path, measured on both images). IMAGE-FREE (a Theorem Labs lane lib/B closure rule): this file Requires no image module and no PcapRelro, so lib/B can state its twin from the same generic text; lib/A's data moved to PcapEntryA.v. *)
(* LLVMFuzzerTestOneInput's image-A entry contract for reac-pw/fuzz_link (fuzz_link.asan, the PUBLISHED pin,
   sha256 059dae63e07c...; listing (internal path)
   (internal record, sha256 e84d6f0c6974)), in the slot shape the ASan driver consumes: pcap's tfib_lib_contract_x
   (lib/A/Prog/PcapEntry.v on origin/ossv/recipes 3abc3740de97, lines 41-83) in fuzz_grant's / boxreg's fx-slot form
   (boxreg lib/A/ACfn.v:80-131 on the same ref: tfib_lib_contract_xP P, the zero rounding mode in and out
   tfib_lib_contract_xf, the bridge tfib_lib_contract_xP_of_xf).
   Image-free: every image datum is a Section variable; link's values and the instance are in LinkEntryA.v.

   What changes from pcap's text, and why (each from the image-A listing or from the lib/A frame):
   - The call keeps link's memory FILE across target calls (mark_quietly opens g_sink with fmemopen on the first
     mark and nothing closes it: link.asan has no fclose). pcap's read source (asource_none, asrc_meta_inv over
     pcap_KS, as_ofl_head KS = AOFL_HEAD) is replaced by a Theorem Labs lane's A memory-FILE invariant (lib/A/AMemFileSink.v):
     the kept blocks T of the call's start, amf_gi MS T (the three heads g_sink / g_say / ofl_head are 0 and
     T = [], or they hold the one kept block f, T = [(f, 1304)], and f is a memory FILE over g_said), the kept
     blocks live in the ledger (incl T (ablocks B ly S)), the three stdio words of amf_env, and the head law
     amf_head_law SK MS (the FILE list head the journal spares is MS's). The post has the pairing rule of
     AMemFileSink.v: amf_blocks_post T T' with amf_gi MS T' at the same return, in place of pcap's
     Permutation (ablocks B ly' S') (ablocks B ly S). The journal's footprint is amf_harness_fp T (pcap's
     [sink_token], plus the kept block's range once the FILE is open: AMemFile.v amf_harness_fp_grants).
   - The NUL at msg_build.long_alias[300] (la_nul): kernel's Pre reads long_alias through its NUL
     (lib/A/Prog/kernel_c.v kernel_apre, `au8arr ... LA_LONG_ALIAS (la ++ [zb 0])`, the strlen of msg_build), and
     long_alias is in G, so the contract carries that byte from one target call to the next (the plain contract's
     GI, lib/Prog/LLVMFuzzerTestOneInput_c.v llvm_GI, carries the same byte).
   - The wild-trace room (ruling of 09:59Z; lib/A/LinkWildRoom.v): pre link_wild_room
     (96 wild traces of room: 2 text_of calls per op, 48 ops); post, as a count, the depot's wild part grows by at
     most LINK_WILD_PER_CALL (the callees' LedPost are counts: text_of_c.v, text_buf_c.v, mark_quietly's; no callee
     states a run of depot puts). link_wild_room_count below is the driver's sum over its 1-4 calls in this form.
   - pcap's arodata_okS is stated as Reusable/YC20.v's arodata_okP (the same body; the form every callee contract
     uses). pcap's `fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None` is dropped: no instruction of link's call and
     no callee needs it, because link opens no file descriptor on its path: its sockets are the harness's fake ones
     (fuzz_socket returns 7 with no system call), fmemopen allocates memory only, and no own function contains an
     ecall; the fd-creating ecalls the reached runtime and libc code holds (openat 0x65f20 / 0x9d998, dup 0x65fd4,
     dup3 0x65fe4, socket 0x9592c / 0x9597c, pipe2 0xa02f0) lie behind runtime-state gates inside callees the walk
     applies by contracts that keep the descriptor table (ecall census with its a7 values and controls:
     link-a/slot/stderr-scan/RESULT.md (internal record, sha256 7bc6c60cd0d5) section 7).
   - The library shape is ZTraceSpec.checksum_shape, the LIBK of the plain contract's mf_shape
     (lib/MemFileRI.v: LIBK := @LIBK checksum_shape): the call returns 0 and writes nothing
     (LIBK pl fs K = K (LL 0 fs [])); the post states ll_ret l = 0 and ll_out l = [] as pcap's does.
   - The float state (boxreg's slot forms; the zero rounding mode at entry is a separate premise of tfib_lib_contract_xf,
     and there are no boxreg `_x` forms with the fxr clause, which no consumer of link's slot needs): the call is
     entered at a zero rounding mode and returns at some fx' with a zero rounding mode (the snprintf / vfprintf
     callees' posts lose fa0, link-a/float/REPORT.md (internal record, sha256 af82d0a7a4b0) answer 1; 0 writers
     of frm / fcsr in link.asan's .text, link-a/float/scan/RESULT.md (internal record, sha256 bdc4b1bba9ee)).
     tfib_lib_contract_xf is the contract the walk proves (for every fx: tfib_lib_contract_xf_all); tfib_lib_contract_xP
     P is the slot the driver consumes, at P = a zero rounding mode (tfib_lib_contract_xP_of_xf).
   EV_LIB and LIVE_LIB are link's (measured on the image-A listing, sites below); pcap's 10 and 2^26 + 1304 + 2040
   do not carry over. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO09 YI04 YI16 YC20 YC5d YM05 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require ZTraceSpec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile LinkWildRoom.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* EV_LIB: the most allocator events (each a malloc, calloc or free, free(NULL) included) of one call, from the
   image-A listing: the two callocs of the model and the marks (0x82c74 calloc(1, 0x2298), 0x82c84 calloc(1, 0x204))
   and their two frees at the end (0x83b88, 0x83b90); per operation at most 4: op_decide's two text_of (0x82e24,
   0x82e34; EV 1 each, text_of_c.v) and two frees (0x82e6c, 0x82e74), or op_read's two text_buf (0x835f4, 0x83600;
   EV 1 each, text_buf_c.v) and two frees (0x83754, 0x8375c); op_write makes 2 (text_of 0x837d8, free 0x838d8), a
   mark at most 1 (mark_quietly 0x831f8 / 0x8347c: the fmemopen malloc of its open arm, mark_quietly_c.v EV 1);
   every other callee makes none (EV 0 in its contract; the side-stack calls are no allocator events); at most 48
   operations (the loop bound OPS_MAX, fuzz_link.c:75, :777). 2 + 48 * 4 + 2 = 196. *)
Definition EV_LIB : Z := 196.
(* LIVE_LIB: the most live heap bytes the call adds to its caller's: the model (8856 = 0x2298) and the marks
   (516 = 0x204) blocks, the FILE block of the first mark (1304 = 0x518, AMemFileSink.AMF_BLOCK; fmemopen is
   passed g_said, so it makes no second malloc), and one operation's text blocks, freed by the same operation:
   op_decide's two text_of blocks (each request at most 320, text_of_c.v TEXT_OF_LIVE) are the largest pair
   (op_read's two text_buf blocks are at most 40 each, op_write's one text_of block at most 320). *)
Definition LIVE_LIB : Z := 8856 + 516 + 1304 + 2 * 320.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* The image: its loaded segments, its read-only window, the entry function's address, the return address into
   target_run, the driver's pointer for an empty input, and the stack the call needs. *)
Variable segs : list Segment.
Variables rlo rhi : Z.
Variables a_llvmf ra_llvmf a_empty stk : Z.
(* The program-global ranges the call may change: W_journalG.v's ajournal_gx G. *)
Variable G : list (Z * Z).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
(* The memory FILE's record (AMemFileSink.v amemfile_syms) and the address of long_alias's NUL. *)
Variable MS : amemfile_syms.
Variable la_nul : Z.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation LS := ZTraceSpec.checksum_shape.
Definition tfib_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (T : list (Z * Z)) : Prop :=
afn_pre segs B stk ly S W regs mem md [] /\
raZ regs = ra_llvmf /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = a_empty) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) /\
(* link's memory FILE, kept across target calls (in place of pcap's read source) *)
amf_gi segs MS T (rd W mem) /\ incl T (ablocks B ly S) /\ (0 < n -> ~ In (p, n) T) /\
amf_env segs MS (rd W mem) /\ amf_head_law SK MS /\
(* the NUL that ends long_alias *)
val_mem segs (rd W mem) la_nul 1 0 /\
(* the inert fd-names invariant, carried as pcap carries it (PcapEntry.v:52-54): link opens nothing by name *)
Namei.fd_names_path (m_fds md) YI16.sink_path = false /\
Fs.fs_sorted (m_fs md) = true /\
mo_ok MT S (XM_LIB n) /\
link_wild_room (as_universe B) S.
Definition tfib_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (T : list (Z * Z)) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z)
(T' : list (Z * Z)) : Prop :=
ajournal_gx segs B G 0 [] stk (spZ regs) (amf_harness_fp T) ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
(* the kept blocks: AMemFileSink.v's pairing rule, amf_blocks_post with amf_gi at the same return *)
amf_blocks_post T T' (ablocks B ly S) (ablocks B ly' S') /\
amf_gi segs MS T' (rd W' mem') /\ amf_env segs MS (rd W' mem') /\
val_mem segs (rd W' mem') la_nul 1 0 /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
(* the same invariant at the end (PcapEntry.v:65-67) *)
Namei.fd_names_path (m_fds md') YI16.sink_path = false /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
mo_le MT S S' (XN_LIB n) /\
(length (wild_part (as_universe B) (st_depot S')) <=
  length (wild_part (as_universe B) (st_depot S)) + LINK_WILD_PER_CALL)%nat /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
(* The slot with the float state at return left open (boxreg ACfn.v:80-92): the call returns at some float state
   fx' with P, and the driver goes on at fx'. *)
Definition tfib_lib_contract_xP (P : YK11.FPState -> Prop) : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl T (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl T ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k T',
c' = mkCfg (@YK11.mkst fx' regs' (w64 ra_llvmf) mem' (YK11.seg_rom segs)) md' /\ P fx' /\
tfib_lib_post_x regs ly S W mem md p n T l ly' S' W' regs' mem' md' k T') ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs a_llvmf regs mem md) (@LIBK LS pl (m_fs md) K).
(* The exists-fx' form (boxreg ACfn.v:93-110): entered at a zero rounding mode, it returns at some float state fx'
   with a zero rounding mode. This is the contract LLVMFuzzerTestOneInput's walk proves. *)
Definition tfib_lib_contract_xf : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl T (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl T -> YK0o.frm_zero (@fp_csr fx) ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k T',
c' = mkCfg (@YK11.mkst fx' regs' (w64 ra_llvmf) mem' (YK11.seg_rom segs)) md' /\
YK0o.frm_zero (@fp_csr fx') /\
tfib_lib_post_x regs ly S W mem md p n T l ly' S' W' regs' mem' md' k T') ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs a_llvmf regs mem md) (@LIBK LS pl (m_fs md) K).
(* The exists-fx' slot, entered at a zero rounding mode (boxreg ACfn.v:123-131). *)
Lemma tfib_lib_contract_xP_of_xf : YK0o.frm_zero (@fp_csr fx) -> tfib_lib_contract_xf ->
tfib_lib_contract_xP (fun f : YK11.FPState => YK0o.frm_zero (@fp_csr f)).
Proof.
intros Hz LIBF ly S W regs mem md p n pl T K HAI HPRE CONT.
apply (LIBF ly S W regs mem md p n pl T K HAI HPRE Hz).
intros l W' c' Hwle HAI' (fx' & ly' & S' & regs' & mem' & md' & k & T' & Hc & Hz' & HPOST).
apply (CONT l W' c' Hwle HAI'). exists fx', ly', S', regs', mem', md', k, T'. exact (conj Hc (conj Hz' HPOST)).
Qed.
End a.
(* The sink head is EXPLICIT on every exported statement, as in pcap's PcapEntry.v:85-90: the only global
   sink_head instance in this closure is the plain build's (lib/Reusable/YI5b.v src0_sink_head), whose head is not
   the ASan image's. *)
Arguments tfib_lib_pre_x {rc} SK.
Arguments tfib_lib_post_x {rc} SK.
Arguments tfib_lib_contract_xP {fx rc} SK.
Arguments tfib_lib_contract_xf {fx rc} SK.
Arguments tfib_lib_contract_xP_of_xf {fx rc} SK.
(* The driver's sum over its calls, in the post's count form (the form of LinkWildRoom.v link_wild_room_calls):
   from a depot whose wild part holds at most i * 96 traces, with i < 4 calls made and room for 4 * 96, the next call
   has its room. *)
Lemma link_wild_room_count : forall (U : Univ) (s : astate) (i : nat),
  (length (wild_part U (st_depot s)) <= i * LINK_WILD_PER_CALL)%nat -> (i < LINK_CALLS_MAX)%nat ->
  (LINK_CALLS_MAX * LINK_WILD_PER_CALL <= u_wmax U)%nat -> link_wild_room U s.
Proof. intros U s i Hw Hi Hr. unfold link_wild_room, LINK_CALLS_MAX, LINK_WILD_PER_CALL in *. nia. Qed.
(* One call's step of the same count. *)
Lemma link_wild_count_step : forall (U : Univ) (s s' : astate) (i : nat),
  (length (wild_part U (st_depot s)) <= i * LINK_WILD_PER_CALL)%nat ->
  (length (wild_part U (st_depot s')) <= length (wild_part U (st_depot s)) + LINK_WILD_PER_CALL)%nat ->
  (length (wild_part U (st_depot s')) <= Datatypes.S i * LINK_WILD_PER_CALL)%nat.
Proof. intros U s s' i H1 H2. unfold LINK_WILD_PER_CALL in *. lia. Qed.
Definition tfib_lib_contract_xf_all {rc : YM05.RunCeil} (SK : YI16.sink_head) (segs : list Segment) (rlo rhi : Z)
(a_llvmf ra_llvmf a_empty stk : Z) (G : list (Z * Z)) (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z)
(MS : amemfile_syms) (la_nul : Z) : Prop :=
forall fx : YK11.FPState,
@tfib_lib_contract_xf fx rc SK segs rlo rhi a_llvmf ra_llvmf a_empty stk G B MT XM_LIB XN_LIB MS la_nul.
(* GUARD (pcap PcapEntry.v:95-101): SK is passed by position; if it went back to implicit, instance search would
   fill it and the positional SK would land on the next argument, so this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  tfib_lib_contract_xf (fx:=fx) (rc:=rc) SK).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  tfib_lib_contract_xP (fx:=fx) (rc:=rc) SK).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_pre_x (rc:=rc) SK).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_post_x (rc:=rc) SK).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_contract_xf_all (rc:=rc) SK).
