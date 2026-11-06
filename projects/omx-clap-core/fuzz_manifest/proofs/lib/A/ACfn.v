(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: relocated from cgif_file_fuzzer.asan to omx-clap-core fuzz_manifest.asan: 3 address literal(s) rewritten, module paths changed; tfib_lib_post_x's journal footprint is sink_token :: FM_PSTAT_FP (A/FMPstat.v): fuzz_manifest's LLVMFuzzerTestOneInput writes the four statics of fuzz/alloc.c; EV_LIB is 2100 (fuzz_manifest's per-call worst case is 2,060 events); the contract (now tfib_lib_contract_xI) carries a library invariant LI over the calls: call ci (0 <= ci < 4) needs LI ci and gives LI (ci + 1). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO09.
From OSSVerify.omx_clap_core.fuzz_manifest.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMPstat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_LLVMF : Z := 0x8091c.
Definition RA_LLVMF : Z := 0x80818.
Definition A_EMPTY : Z := 0x5d43e0.
Definition EV_LIB : Z := 2100.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition LLVMF_STK : Z := 32768.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Variable LI : Z -> world segs -> (word -> option byte) -> Prop.
Definition tfib_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
asink_none segs tfib_K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs tfib_K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n).
Definition tfib_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (M : Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
ajournal segs B LLVMF_STK (spZ regs) (sink_token :: FM_PSTAT_FP) ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K (rd W' mem') md' /\
ameta_inv segs tfib_K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition tfib_lib_contract_xI : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet) (ci : Z),
0 <= ci < 4 -> LI ci W mem ->
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
tfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k /\ LI (ci + 1) W' mem') ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition tfib_lib_contract_xI_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z)
(LI : Z -> world tfibsegs -> (word -> option byte) -> Prop) : Prop :=
forall fx : YK11.FPState, @tfib_lib_contract_xI fx rc LS B MT XM_LIB XN_LIB RLO RHI LI.
