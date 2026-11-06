(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/Q/YW0a.v, with its module names changed; 15 of its 38 lines of code are new or changed and 50 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/Q/YT01.v; 55 of its 76 lines of code are new or changed and 17 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06 YK0s YM02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0g YO0w YO0s YO0u YO15 YO10 YO0t YO0x YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN03 YN2b YN0b_cf YN07_cf YN0a_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.Q Require Import YW03_cf YW0e_cf YW06_cf YW07_cf YW09_cf YW0a_cf YY00_cf YY03_cf YV00_cf YV01_cf YV10_cf YV11_cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM06_cf YO0d_cf YN2b_cf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (g : sptr) (am : ameta) (fr : frame) (n : Z) (a : sptr) (ka : Z) (rg : YO0i.region).
Hypothesis HC : realloc_ctx L A regs mem md g am fr n a ka rg.
Lemma small_via lo hi cs : lo <= n <= hi -> (forall gd err, conds_ok (Er L regs g am fr n a rg gd err) cs) ->
(forall E, st_ok src0segs E (S0n lo hi cs (rcr am fr)) (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)) ->
SR_cfv src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)) md) (arrives E (rcr am fr) mem md)) ->
mreal_cf src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)) md) (realloc_move (pp am fr) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (pp am fr) (fr_n fr) n).
Proof using HC.
intros Hlh Hcs RUN.
destruct (OBL_entry_n L A regs mem md g am fr n a ka rg HC (rcr am fr) (YW06_cf.FP L A regs mem md g am fr n a ka rg HC) lo hi cs Hlh Hcs)
as (gd & err & Hgd & Herr & HS).
eapply mreal_cf_SR_pre; [exact (RUN _ HS)|].
intros c Hc. exact (arrives_fb L A regs mem md g am fr n a ka rg HC gd err Hgd Herr c Hc).
Qed.
Lemma k3b_small_mreal : n < MMAP_THRESHOLD ->
mreal_cf src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_realloc) mem (seg_rom src0segs)) md) (realloc_move (pp am fr) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md (pp am fr) (fr_n fr) n).
Proof using HC.
intros Hs. pose proof (rc_n _ _ _ _ _ _ _ _ _ _ _ _ HC) as Hn. unfold MMAP_THRESHOLD in Hs.
pose proof (MRx_MRc _ _ _ _ _ (proj1 (rc_pre _ _ _ _ _ _ _ _ _ _ _ _ HC))) as M.
destruct (mc_md _ _ _ _ _ M) as (Hh & Hlz & _).
pose proof (mc_statics _ _ _ _ _ M) as ST.
destruct (cond_split L regs g am fr n a rg) as [HL | HG].
- apply (small_via 0 131051 [condLT]); [lia | exact HL |].
intros E HS. exact (k3b_small_gt E (rcr am fr) _ md HS Hh Hlz).
- destruct (Z_lt_le_dec n 157) as [H157 | H157].
+ apply (small_via 0 156 [condGE]); [lia | exact HG |].
intros E HS. exact (k3b_small_le157 E (rcr am fr) _ md HS Hh Hlz).
+ apply (small_via 157 131051 [condGE]); [lia | exact HG |].
intros E HS. exact (k3b_small_big E (rcr am fr) _ md HS ST Hh Hlz).
Qed.
End b.
Theorem realloc_k3b :
forall pc L A regs mem md p nold n g am idx fr,
ms_realloc src0_msyms = Some pc ->
call_pre_k src0_msyms (MRx src0_msyms) REALLOC_STACK L A regs mem md ->
In (p, nold) (user_blocks A) ->
getr regs 10 = Z_to_bv 64 (ptr_addr L p) -> getr regs 11 = Z_to_bv 64 n ->
0 <= n < 2 ^ 62 ->
usedX [] A g am -> 0 <= idx <= am_last am -> ss_fr (nth_slot am idx) = Some fr -> fr_kind fr = FUser ->
fr_n fr = nold -> p = frame_ptr am idx fr -> am_sc am = 63 ->
mreal_cf (ms_segs src0_msyms) (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom (ms_segs src0_msyms))) md)
(realloc (Some p) n A)
(realloc_leaf src0_msyms (MRx src0_msyms) L A regs mem md p nold n).
Proof using.
intros pc L A regs mem md p nold n g am idx fr Hpc PRE Hin Ha0 Ha1 Hn Hu Hidx Hfr Hk Hno Hp H63.
destruct (Z_lt_le_dec n MMAP_THRESHOLD) as [Hs | Hb].
2:{ exact (src0_realloc_k3b_big realloc_fb_gen pc L A regs mem md p nold n g am idx fr Hpc PRE Hin Ha0 Ha1
(conj Hb (proj2 Hn)) Hu Hidx Hfr Hk Hno Hp H63). }
cbn [ms_realloc src0_msyms] in Hpc. injection Hpc as <-.
destruct (realloc_ctx_of L A regs mem md p nold n g am idx fr PRE Hin Ha0 Ha1 Hn Hu Hidx Hfr Hk Hno Hp H63)
as (-> & a & ka & rg & HC).
subst p nold. change (ms_segs src0_msyms) with src0segs.
pose proof (mc_wf _ _ _ _ _ (MRx_MRc _ _ _ _ _ (proj1 PRE))) as HW.
rewrite (realloc_small_tree A g am fr n HW Hu Hfr H63 (rc_last _ _ _ _ _ _ _ _ _ _ _ _ HC) ltac:(lia)).
exact (k3b_small_mreal L A regs mem md g am fr n a ka rg HC Hs).
Qed.
End a.
