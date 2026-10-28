(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO09.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_LLVMF : Z := 0x80490.
Definition RA_LLVMF : Z := 0x8038c.
Definition A_EMPTY : Z := 0x5d8660.
Definition EV_LIB : Z := 2000.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition LLVMF_STK : Z := 32768.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
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
ajournal segs B LLVMF_STK (spZ regs) [sink_token] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks B ly' S') (ablocks B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
asink_none segs tfib_K (rd W' mem') md' /\
ameta_inv segs tfib_K ly' (rd W' mem') M /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)).
Definition tfib_lib_contract_x : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists ly' S' regs' mem' md' k,
c' = cfg_at segs RA_LLVMF regs' mem' md' /\
tfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
End a.
Definition tfib_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @tfib_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.
