(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACfn.v at 25e3d17bdb50, with its module paths changed, its addresses moved to libreac/fuzz_grant's ASan build and A_LLVMF set to fuzz_grant's LLVMFuzzerTestOneInput. *)
(* Modified by Theorem Labs, 2026-10: added the slot with the float state at return left open (tfib_lib_contract_xP), cgif's exists-fx' form of it (tfib_lib_contract_xf, lib/YL0g.v:58-64) and the two lemmas that carry tfib_lib_contract_x and tfib_lib_contract_xf into it. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/A/ACfn.v at 4f87de75d67 (donor image sha256 c2c7559b29bd), with its module paths changed and its addresses moved to reac-repacer/fuzz_wire's ASan build. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YO09.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import Asan.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import AE2k.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK0o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_LLVMF : Z := 0x7fe58.
Definition RA_LLVMF : Z := 0x7fd54.
Definition A_EMPTY : Z := 0x5d2de0.
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
(* The slot with the float state at return left open: LLVMFuzzerTestOneInput returns at some float state fx' that
   satisfies P, and the driver goes on at fx'. P = (fun f => f = fx) is tfib_lib_contract_x (tfib_lib_contract_xP_pinned);
   P = (fun f => frm_zero (fp_csr f)) is tfib_lib_contract_xf (tfib_lib_contract_xP_of_xf). *)
Definition tfib_lib_contract_xP (P : YK11.FPState -> Prop) : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_x regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\ P fx' /\
tfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
(* cgif's exists-fx' form (lib/YL0g.v:58-64 lib_contract) of tfib_lib_contract_x, for an entry function that may change
   the float registers: the entry asks a zero rounding mode, and the return is at some float state fx' with a zero
   rounding mode. tfib_lib_pre_xf is tfib_lib_pre_x with the zero rounding mode as its last conjunct. *)
Definition tfib_lib_pre_xf (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (M : Z) : Prop :=
afn_pre segs B LLVMF_STK ly S W regs mem md [] /\
raZ regs = RA_LLVMF /\
YK11.getr regs 10 = w64 p /\ YK11.getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
arodata_okS segs B RLO RHI (aview segs (w_H W) mem) /\
asink_none segs tfib_K (rd W mem) md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
ameta_inv segs tfib_K ly (rd W mem) M /\
mo_ok MT S (XM_LIB n) /\
frm_zero (@fp_csr fx).
Definition tfib_lib_contract_xf : Prop :=
forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
tfib_lib_pre_xf regs ly S W mem md p n pl M ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
tfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).
(* The pinned slot returns at fx itself. *)
Lemma tfib_lib_contract_xP_pinned : forall P : YK11.FPState -> Prop, P fx -> tfib_lib_contract_x -> tfib_lib_contract_xP P.
Proof.
intros P HP LIBC ly S W regs mem md p n pl M K HAI HPRE CONT.
apply (LIBC ly S W regs mem md p n pl M K HAI HPRE).
intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Hc & HPOST).
apply (CONT l W' c' Hwle HAI'). exists fx, ly', S', regs', mem', md', k. exact (conj Hc (conj HP HPOST)).
Qed.
(* The exists-fx' slot, entered at a zero rounding mode. *)
Lemma tfib_lib_contract_xP_of_xf : frm_zero (@fp_csr fx) -> tfib_lib_contract_xf ->
tfib_lib_contract_xP (fun f : YK11.FPState => frm_zero (@fp_csr f)).
Proof.
intros Hz LIBF ly S W regs mem md p n pl M K HAI HPRE CONT.
apply (LIBF ly S W regs mem md p n pl M K HAI).
- destruct HPRE as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16).
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
(conj H13 (conj H14 (conj H15 (conj H16 Hz)))))))))))))))).
- intros l W' c' Hwle HAI' (fx' & ly' & S' & regs' & mem' & md' & k & Hc & Hz' & HPOST).
apply (CONT l W' c' Hwle HAI'). exists fx', ly', S', regs', mem', md', k. exact (conj Hc (conj Hz' HPOST)).
Qed.
End a.
Definition tfib_lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @tfib_lib_contract_x fx rc LS B MT XM_LIB XN_LIB RLO RHI.
Definition tfib_lib_contract_xf_all {rc : YM05.RunCeil} {LS : lib_shape} (B : asyms) (MT : ameter_ops) (XM_LIB XN_LIB : Z -> Z) (RLO RHI : Z) : Prop :=
forall fx : YK11.FPState, @tfib_lib_contract_xf fx rc LS B MT XM_LIB XN_LIB RLO RHI.
