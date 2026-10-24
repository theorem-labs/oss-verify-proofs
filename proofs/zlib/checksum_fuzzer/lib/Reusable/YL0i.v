(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei Open.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Section d.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.
Definition lib_pre_x (stk empty : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (ra p n : Z) (pl : list byte) (b : rbound) : Prop :=
lib_pre B API stk empty L A regs mem md ra p n /\
n = Z.of_nat (length pl) /\ blk_data B mem p pl /\
res_ok A b /\ lib_room b n /\
sink_none B mem md /\
fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
Fs.fs_sorted (m_fs md) = true /\
spZ regs <= 2 ^ 47.
Definition lib_post_x (stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p n : Z) (b : rbound) (l : lleaf)
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
regs_preserved regs regs' /\
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
(forall q k, In (q, k) (user_blocks A) -> exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
sink_none B mem' md' /\
res_ok A' (lib_delta n b) /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)).
Definition lib_contract_x (pc ra empty stk : Z) : Prop :=
forall L A regs mem md p n pl b (K : lleaf -> TSet),
lib_pre_x stk empty L A regs mem md ra p n pl b ->
frm_zero fp_csr ->
(forall (l : lleaf) (c' : config),
(exists (fx' : FPState) L' A' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
frm_zero (@fp_csr fx') /\
lib_post_x stk L A regs mem md p n b l L' A' regs' mem' md') ->
realizes segs c' (K l)) ->
realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).
Definition md_rebase (md : Model) (fds' : _) (fs' : Fs) (pins' : _) : Model := os_upd (m_vmmaps md) fds' fs' pins' md.
Lemma lib_post_of_x : forall stk L A regs mem md p n b l L' A' regs' mem' md',
lib_post_x stk L A regs mem md p n b l L' A' regs' mem' md' ->
exists fds' pins', lib_post B API stk L A regs mem (md_rebase md fds' (ll_fs l) pins') p L' A' regs' mem' md'.
Proof.
intros stk L A regs mem md p n b l L' A' regs' mem' md'
(H1 & H2 & H3 & H4 & H5 & H6 & (vm' & fds' & pins' & Hmd & Hfds) & H8 & H9 & H10 & H11 & H12 & _).
exists fds', pins'. unfold lib_post. repeat (split; [assumption|]). split; [|repeat (split; [assumption|]); exact H12].
exists vm'. rewrite Hmd. unfold md_rebase. rewrite with_vmmaps_os_upd, os_upd_twice. reflexivity.
Qed.
Lemma MR_rebase : MR_laws B MR -> forall L A mem md fds' fs' pins', MR L A mem md -> MR L A mem (md_rebase md fds' fs' pins').
Proof.
intros LAWS L A mem md fds' fs' pins' H. destruct (mr_model B MR LAWS _ _ _ _ H) as (Hh & Hlz & Hmat).
apply (mr_frame B MR LAWS L A mem mem md (md_rebase md fds' fs' pins') H); auto.
intros p n i Hin Hi. exact (proj1 (mr_blocks B MR LAWS L A mem md p n i H Hin Hi)).
Qed.
End d.
End c.
Definition lib_contract_x_all {rc : YM05.RunCeil} {LS : lib_shape} (B : malloc_syms) (API : AllocAPI B) {SH : sink_head} {SK : sink_syms}
(pc ra empty stk : Z) : Prop :=
forall fx : FPState, @lib_contract_x fx rc LS B API SH SK pc ra empty stk.
