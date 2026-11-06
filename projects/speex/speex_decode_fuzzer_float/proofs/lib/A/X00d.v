(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1rn X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X00a X001 X00b X00c X000 X00l X00h
X00e X00f X00g.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0e7.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r9 X0r0 X0ra X0rb X0qz X0rk X0rg X0rd X0re X0rf.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14s.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rb OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0qz OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rg OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0re OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0rf.
Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14s.
Import ListNotations.
Open Scope Z_scope.

Section Loop.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis HDATA : fs_lookup fs (path_b argvb) = Some data.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_okF RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_fileF RT.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Lemma RL_len : forall len cap c, RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c -> 0 <= len <= Z.of_nat (length data).
Proof.
intros len cap c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hlen & Hld & _). lia.
Qed.

Lemma RGROW_len : forall len cap c, RGROW RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c -> 0 <= len < cap /\ cap <= Z.of_nat (length data).
Proof.
intros len cap c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hlc & Hcd & _). lia.
Qed.

Theorem read_loop : forall len cap,
cps bsegs (RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap)
(fun c => RDONE RT OUT_rep ERR_rep XENV LIB argvb fs data c \/ RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data c).
Proof using HDATA AF AF_DRV MAL FRE MCP RFILE OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
intros len cap T c HR Hk.
assert (G : forall k len cap c, Z.to_nat (Z.of_nat (length data) - len) = k ->
RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c -> realizes bsegs c T).
{ intros k. induction k as [k IH] using lt_wf_ind. intros len0 cap0 c0 Hk0 HR0.
pose proof (RL_len len0 cap0 c0 HR0) as L0.
apply (seg_read RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data HDATA AF RFILE OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
len0 cap0 T c0 HR0).
intros c1 [HD|HM]; [apply Hk; left; exact HD|].
apply (seg_mem RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF AF_DRV MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
len0 cap0 T c1 HM).
intros c2 [(len' & Hlt & HR2)|[HT|HG]].
- pose proof (RL_len len' cap0 c2 HR2) as L2.
apply (IH (Z.to_nat (Z.of_nat (length data) - len'))) with len' cap0; [lia| reflexivity| exact HR2].
- apply Hk. right. exact HT.
- pose proof (RGROW_len len0 cap0 c2 HG) as L2.
apply (seg_grow RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF MAL FRE MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
len0 cap0 T c2 HG).
intros c3 HR3.
apply (IH (Z.to_nat (Z.of_nat (length data) - cap0))) with cap0 (2 * cap0); [lia| reflexivity| exact HR3]. }
exact (G _ len cap c eq_refl HR).
Qed.

End Loop.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section Loop.
Variable RT : rt_sig.
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Variable XENV : mem -> Prop.
Variable XENV_FP : list (Z * Z).
Variable LIB : mem -> Prop.
Variable argvb : list (list byte).
Variable fs : Fs.
Variable data : list byte.
Hypothesis HDATA : fs_lookup fs (path_b argvb) = Some data.
Hypothesis AF : art_facts RT.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis MAL : malloc_contract_okF RT.
Hypothesis FRE : free_contract_okF RT.
Hypothesis MCP : memcpy_icontract RT e_memcpy.
Hypothesis RFILE : read_icontract_fileF RT.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis XENV_loc : fp_local XENV_FP XENV.
Hypothesis LIB_loc : fp_local LIB_FP LIB.
Hypothesis IO_img : forall x, in_ranges IO_FP x -> client_static x /\ ~ drv_cell x /\ outside LIB_FP x.
Hypothesis XENV_img : forall x, in_ranges XENV_FP x -> client_static x /\ ~ drv_cell x /\ outside IO_FP x /\ outside LIB_FP x.

Lemma RL_len : forall len cap c, RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c -> 0 <= len <= Z.of_nat (length data).
Proof.
intros len cap c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hlen & Hld & _). lia.
Qed.

Lemma RGROW_len : forall len cap c, RGROW RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c -> 0 <= len < cap /\ cap <= Z.of_nat (length data).
Proof.
intros len cap c (Σ & usp & ap & path & buf & gp & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6
& c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & F & fc & m & _ & _ & _ & _ & Hlc & Hcd & _). lia.
Qed.

Theorem read_loop : forall len cap,
cps asegs (RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap)
(fun c => RDONE RT OUT_rep ERR_rep XENV LIB argvb fs data c \/ RTOOBIG RT OUT_rep ERR_rep XENV LIB argvb fs data c).
Proof using HDATA AF AF_DRV MAL FRE MCP RFILE OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img.
intros len cap T c HR Hk.
assert (G : forall k len cap c, Z.to_nat (Z.of_nat (length data) - len) = k ->
RL RT OUT_rep ERR_rep XENV LIB argvb fs data len cap c -> realizes asegs c T).
{ intros k. induction k as [k IH] using lt_wf_ind. intros len0 cap0 c0 Hk0 HR0.
pose proof (RL_len len0 cap0 c0 HR0) as L0.
apply (seg_read RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data HDATA AF RFILE OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
len0 cap0 T c0 HR0).
intros c1 [HD|HM]; [apply Hk; left; exact HD|].
apply (seg_mem RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF AF_DRV MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
len0 cap0 T c1 HM).
intros c2 [(len' & Hlt & HR2)|[HT|HG]].
- pose proof (RL_len len' cap0 c2 HR2) as L2.
apply (IH (Z.to_nat (Z.of_nat (length data) - len'))) with len' cap0; [lia| reflexivity| exact HR2].
- apply Hk. right. exact HT.
- pose proof (RGROW_len len0 cap0 c2 HG) as L2.
apply (seg_grow RT OUT_rep ERR_rep IO_FP XENV XENV_FP LIB argvb fs data AF MAL FRE MCP OUT_loc ERR_loc XENV_loc LIB_loc IO_img XENV_img
len0 cap0 T c2 HG).
intros c3 HR3.
apply (IH (Z.to_nat (Z.of_nat (length data) - cap0))) with cap0 (2 * cap0); [lia| reflexivity| exact HR3]. }
exact (G _ len cap c eq_refl HR).
Qed.

End Loop.
