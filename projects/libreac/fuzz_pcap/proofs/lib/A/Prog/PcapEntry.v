(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfn.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_pcap on libreac v1.9.0, ASan build (image root: the original v1.9.0 set, the pinned fuzz_pcap.asan image, sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin fuzz_pcap.asan (sha256 36da3052c383); capstone disassembly); module paths changed. Relocated constants (the image's own, A_LLVMF / RA_LLVMF / A_EMPTY / LLVMF_STK / G_HARNESS, with their measurements, are in lib/A/Prog/PcapEntryA.v): EV_LIB = 10 (allocator events of the worst path, each a malloc, free or free(NULL): malloc 0x80940, the malloc of musl fmemopen 0x8e908 under pcap_source_open 0x8099c, malloc 0x80ab8, fclose's free(NULL) 0x8e2b4 and free 0x8e2bc under pcap_source_close 0x810a8, malloc 0x8e908 under pcap_source_open 0x810c4, the two frees of fclose under pcap_source_close 0x810e8, free 0x8110c, free 0x81114; a refused file makes 5 and an abort path at most 8; pcap_source_next and the side-stack calls make none); LIVE_LIB = 2^26 + 1304 + 2040 (the bytes the call may hold at once beyond its caller's: the copy of the file, size - 1 <= 2^26 - 2 bytes (0x80914, malloc 0x80940), one 1304-byte FILE block (musl fmemopen 0x8e904 `addi a0,zero,0x518`; close #1 frees it before the reopen allocates the next), the record buffer max(cap, 1) <= 2040 bytes (0x80aa8 `slli s5,a1,3` of one input byte, 0x80ab4)). The library shape is fuzz_pcap's agreement shape AgreePcap.ag_out_shape (lib/AgreePcap.v:26, the shape of the released plain entry contract and of lib/PcapAsanTop.v's pcap_shape) in place of cgif's Context lib_shape, written as its LIBK's own shape, the plain lib/OutForm.v's out_shape PWalk.OUT (ag_out_shape = AgreeShape.ag_shape (out_shape PWalk.OUT) and AgreeShape.ag_LIBK is reflexivity, so the two LIBK terms are convertible): AgreePcap and AgreeShape are not Required here because they load every image module. cgif's write sink (asink_none) is replaced by fuzz_pcap's read-stream state asource_none (lib/A/Stdio/PSource.v) over a Section variable KS : asource_syms, with the premise as_ofl_head KS = AOFL_HEAD that the fmemopen wrapper's statement asks; the image segments are fuzz_pcap's Asan.M.loaded_segments; the meta-region invariant is the source-side asrc_meta_inv segs KS (lib/A/Stdio/PSourceMeta.v, body identical to cgif's ameta_inv with ak_ -> as_), so cgif's sink record tfib_K is gone and tfib_lib_contract_x_all takes KS (and the sink head {SK}) beyond ACfn.v's arguments; the donor's fd-names conjunct of asink_none (YE00.v:124, fd_names_path (m_fds md) sink_path = false) is carried as the INERT fd-names invariant on the pre and the post (cgif's sink path stays a literal; pcap never opens it), since fuzz_pcap opens no descriptor by name (libreac_fuzz_fopen's callees are the strcmp wrapper 0x80760 and the fmemopen wrapper, tail jump 0x807ac; its fopen tail jump 0x80780 is reached only by 0x80750 (path NULL) or 0x80764 (strcmp nonzero), both refuted by its premises: the path is the literal 0x20d00 and the string is equal); SK is a Section variable, EXPLICIT on every exported statement (Arguments below: the only global sink_head instance in this closure is the plain build's, so it must never be inferred), and at ossv/recipes 25e3d17bdb50 (2026-10-29), no released file defined fuzz_pcap's relocated AB1v / AE2k. The post's output is cgif's ll_out l = [] restated as ll_out l = PWalk.OUT pl (lib/Prog/Slot/PWalk.v:205), the output the agreement shape's LIBK hands its continuation (LIBK pl fs K = wr ch_stderr (OUT pl) (K (LL 0 fs (OUT pl)))), so tfib_lib_post_x takes pl after n; PcapEntryDefs.v proves PWalk.OUT pl = [] (pcap_OUT_nil: v1.9.0's reader prints nothing), which a walk uses to meet it. IMAGE-GENERIC (a Theorem Labs lane ruling): the contract text is one for both images; every image datum it names is a Section variable (segs, the read-only window rlo / rhi, a_llvmf, ra_llvmf, a_empty, and the stack bound stk, a composition over the image's own frames), and the harness's global ranges G); lib/A's values and the lib/A instance tfib_lib_contract_x_all_A (segs := Asan.M.loaded_segments, rlo / rhi := PcapRelro.PCAP_RLO / PCAP_RHI, G := G_HARNESS = [(0x5d3f40, 8); (0x5d3f60, 8)]) are in lib/A/Prog/PcapEntryA.v. HARNESS GLOBALS (a Theorem Labs lane decision): the post's journal is W_journal.v's ajournal_gx segs B G 0 [] (the donor's ajournal relative to a start memory that agrees with the true one outside G; XO = 0 and OUT = [], no out-parameter), because the harness writes g_file / g_file_len, which are not in as_owned_static. EV_LIB and LIVE_LIB stay shared constants: the allocator calls and their sizes are the same in both builds (pcap-sizes.md (sha256 28001d79f5f0; internal record), measured on both images). IMAGE-FREE (a Theorem Labs lane lib/B closure rule): this file Requires no image module and no PcapRelro, so lib/B can state its twin from the same generic text; lib/A's data moved to PcapEntryA.v. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
(* The journal with program-global ranges G (copied by path from fuzz_reply, a working branch 6328acea202). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition EV_LIB : Z := 10.
Definition LIVE_LIB : Z := 2 ^ 26 + 1304 + 2040.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* The image: its loaded segments, its read-only window, the entry function's address, the return address into
   target_run, the driver's pointer for an empty input, and the stack the call needs. *)
Variable segs : list Segment.
Variables rlo rhi : Z.
Variables a_llvmf ra_llvmf a_empty stk : Z.
(* The program-global ranges the call may change (the harness's g_file / g_file_len): W_journal.v's ajournal_gx G. *)
Variable G : list (Z * Z).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable KS : asource_syms.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Local Notation LS := (OSSVerify.Proofs.libreac.fuzz_pcap.lib.OutForm.out_shape
  OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT).
Definition tfib_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B stk ly S W regs mem md [] /\
raZ regs = ra_llvmf /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = a_empty) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okS segs B rlo rhi (aview segs (w_H W) mem) /\
asource_none segs KS (rd W mem) /\ as_ofl_head KS = AOFL_HEAD /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
(* the inert fd-names invariant (cgif's asink_none, YE00.v:124 / ACfn.v:42; a Theorem Labs lane 23:43Z, a Theorem Labs lane 00:34Z): no
   descriptor names cgif's sink path; pcap opens nothing by name *)
Namei.fd_names_path (m_fds md) YI16.sink_path = false /\
Fs.fs_sorted (m_fs md) = true /\
asrc_meta_inv segs KS ly (rd W mem) M /\
mo_ok MT S (XM_LIB n).
Definition tfib_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal_gx segs B G 0 [] stk (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
(* the same invariant at the end (cgif ACfn.v:55; the driver destructs it at AD1m.v:55-59 for lib_site_x's pre):
   the per-fd lookup equality does not imply it (fd_names_path folds the whole fd list, LPS Namei.v:188) *)
Namei.fd_names_path (m_fds md') YI16.sink_path = false /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.OUT pl /\ Fs.fs_sorted (ll_fs l) = true /\
asource_none segs KS (rd W' mem') /\
asrc_meta_inv segs KS ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition tfib_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs ra_llvmf regs' mem' md' /\
tfib_lib_post_x regs ly S W mem md p n pl M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs a_llvmf regs mem md) (@LIBK LS pl (m_fs md) K).
End a.
(* The sink head is EXPLICIT on every exported statement (a Theorem Labs lane, 21:57Z): the only global sink_head instance in this
   closure is the plain build's (lib/Reusable/YI5b.v src0_sink_head), whose head is not the ASan image's, so a caller
   that let SK be inferred would state as_ofl_head KS = AOFL_HEAD at the wrong address. *)
Arguments tfib_lib_pre_x {rc} SK.
Arguments tfib_lib_post_x {rc} SK.
Arguments tfib_lib_contract_x {fx rc} SK.
Definition tfib_lib_contract_x_all {rc : YM05.RunCeil} (SK : YI16.sink_head) (segs : list Segment) (rlo rhi : Z)
(a_llvmf ra_llvmf a_empty stk : Z) (G : list (Z * Z)) (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (KS : asource_syms) : Prop :=
forall fx : YK11.FPState,
@tfib_lib_contract_x fx rc SK segs rlo rhi a_llvmf ra_llvmf a_empty stk G B MT XM_LIB XN_LIB KS.
(* GUARD (a Theorem Labs lane): SK is passed by position; if it went back to implicit, instance search would fill
   it and the positional SK would land on the next argument, so this file would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) =>
  tfib_lib_contract_x (fx:=fx) (rc:=rc) SK).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_pre_x (rc:=rc) SK).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_post_x (rc:=rc) SK).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) => tfib_lib_contract_x_all (rc:=rc) SK).
