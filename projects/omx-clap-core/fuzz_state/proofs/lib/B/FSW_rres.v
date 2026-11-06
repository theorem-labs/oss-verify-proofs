(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACer.v:148-161 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh5.v:99 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACja.v:107-117
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-369 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8w.v:289-290 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan build
   (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACai.v:156-159. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec_A.v, with its module paths and module names changed; 1279 of its 1357 lines of code are new or changed and 927 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_K.v from a working branch
   60d0985773d, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/FSW_K.v; 191 of its 280 lines of code are new or changed and 1268 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_rres.v from a working branch
   2767db174a0, same lemma names; imports point at lib/B's image files (YB1v, YB1w, YF0x, FSH_Base, FSH_Rt, FSPstat,
   FSH_Fn_reader and the other lib/B FSW files); the image-agnostic FSupoison, FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma). *)
(* The resume state after a RUNTIME call (strlen, __asan_memcpy, __asan_memset, the poison / unpoison helpers,
   __asan_stack_malloc_N, any callee whose contract gives back ARU and a frame, not a journal): FSW_K's fsw_intrin_atU puts
   the caller's journal back on the memory after the call and keeps ARU there, but builds no symbolic state at the return
   pc. These lemmas build it, for any FP and own of the caller's journal:
   - fsw_resume_after_rtU_chunks: FSW_K's fss_ret (the frame [sp0 - f, sp0) at atom 2 = the resumed sp, its chunks cs);
   - fsw_resume_after_rtU_args_chunks: FSW_ret's fss_retT (fss_ret plus the shadow-base cells and the extra regions rs);
   - fsw_resume_after_rtU_s0_chunks: fss_ret_s0_args (the window [sp0 + lo, sp0 + hi) at atom 8 = s0 = sp0, as FSW_K's
     fss_ret_s0, then extra regions rs that hold on the memory after the call and extra atom facts gf: a stack slot at
     the re-aligned sp by fsw_resume_stack_region_ok; __asan_stack_malloc_N's resume appends its fake frame to rs).
   The _chunks forms take the chunks cs on the machine's memory AFTER the call (a callee that writes inside the caller's
   window, e.g. __asan_memset over a local, gives the new bytes). fsw_resume_after_rtU / _args / _s0 are their
   corollaries for a callee that leaves the window's bytes unchanged: the chunks are read on the machine's memory memT at
   the call and the walker gives that the window bytes are the same after the call on the machine's memory (raw, not
   unpoisoned: a callee that keeps the caller's words through wkeep on mbyte of the raw memory gives it with no unpoison
   bridge). The window bytes are present after the call by the journal's stack-window presence (the window lies in
   [sp0 - STK, sp0)) and ARU. The st_ok half of FSW_K's fsw_after_callU / fsw_after_callU_s0 and FSW_ret's
   fsw_after_callU_args, without the journal composition; the proved instance generalized is a Theorem Labs lane's crcs_resume_sm
   (a working branch c4bfd3bc057, lib/A/FSH_check_reject_clean_starved.v). Owner: a Theorem Labs lane (walk
   kit). A kit: no function's contract is proved here (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* chunks read on memT hold on mem2 when the bytes [base + lo, base + hi) holding them are the same on both *)
Lemma fsw_chunks_kept : forall E (H : word -> bool) memT mem2 base lo hi cs,
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H memT) base) cs ->
  (forall a, base + lo <= a < base + hi -> mbyte tfibsegs (mrestrict H mem2) a = mbyte tfibsegs (mrestrict H memT) a) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict H mem2) base) cs.
Proof.
intros E H memT mem2 base lo hi cs Hin Hcs Hkeep.
apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as [Hc0 Hc1].
apply (chunk_ok_mbyte _ (mrestrict H memT)); [|exact (proj1 (Forall_forall _ _) Hcs c Hc)].
intros i Hi. apply Hkeep. lia.
Qed.

(* the frame region of fss_ret / fss_retT on the memory after the call: the resumed sp (atom 2) is sp0 - f, the window
   [sp0 - f, sp0) is present (the journal's window presence, read on the machine's memory through ARU) *)
Lemma fsw_resume_frame_ok : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k E f cs,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  bv_unsigned (ew E 2) = sp0 - f -> f <= STK ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) mem2) (sp0 - f)) cs ->
  region_ok tfibsegs E (mrestrict (w_H W) mem2) (fstk_ret f cs).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k E f cs HJ HARU E2 Hfs Hcs.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable tfibsegs).
apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
Qed.

(* ---- fss_ret at the return pc r: the env Ereg regs2 extra over the callee's registers regs2 (sp = sp0 - f) and the
   memory mem2 after the call, the chunks cs read on mem2 ---- *)
Lemma fsw_resume_after_rtU_chunks : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k
  regs2 f extra cs r,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  spZ regs2 = sp0 - f -> 0 < f -> f <= STK -> f mod 16 = 0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2) (sp0 - f)) cs ->
  st_ok tfibsegs (Ereg regs2 extra) (fss_ret r f cs)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 f extra cs r HJ HARU Usp Hf Hfs Hal Hwf Hcs.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (E2 : bv_unsigned (ew (Ereg regs2 extra) 2) = sp0 - f)
  by (rewrite (ew_Ereg_nat regs2 extra 2 2%bv eq_refl); exact Usp).
rewrite restrict_mkst_fx. unfold fss_ret. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor].
  exact (fsw_resume_frame_ok B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k _ f cs HJ HARU E2 Hfs Hcs).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
Qed.
(* the sp of regs2 is the call's (callee-saved), the chunks are read at the call on memT and the callee kept the window's
   bytes *)
Lemma fsw_resume_after_rtU : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k
  regsT regs2 memT f extra cs r,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  aregs_preserved regsT regs2 ->
  spZ regsT = sp0 - f -> 0 < f -> f <= STK -> f mod 16 = 0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) memT) (sp0 - f)) cs ->
  (forall a, sp0 - f <= a < sp0 ->
     mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a) ->
  st_ok tfibsegs (Ereg regs2 extra) (fss_ret r f cs)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regsT regs2 memT f extra cs r
  HJ HARU HP Hsp Hf Hfs Hal Hwf Hin Hcs Hkeep.
assert (Esp : getr regs2 2 = getr regsT 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs2 = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
exact (fsw_resume_after_rtU_chunks B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 f extra cs r HJ HARU
  Usp Hf Hfs Hal Hwf (fsw_chunks_kept _ _ memT mem2 (sp0 - f) 0 f cs Hin Hcs (fun a Ha => Hkeep a ltac:(lia)))).
Qed.

(* ---- fss_retT at the return pc r: fss_ret plus the two shadow-base cells (read on mem2 below the shadow, where U2
   changes nothing) and the extra regions rs, under the env Ereg regs2 (fs_extraT ++ xs); the walker's premises for rs
   and gf are FSW_ret fsw_after_callU_args's ---- *)
Lemma fsw_resume_after_rtU_args_chunks : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2
  md2 k regs2 f xs cs rs gf r,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  spZ regs2 = sp0 - f -> 0 < f -> f <= STK -> f mod 16 = 0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) mem2) (sp0 - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) mem2)) rs ->
  pairwise_disjoint (Ereg regs2 (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs2 (fs_extraT ++ xs)) gf ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 f xs cs rs gf r
  Hgot Hcell HJ HARU Usp Hf Hfs Hal Hwf Hcs Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 2) = sp0 - f)
  by (rewrite (ew_Ereg_nat regs2 (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs2 (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
(* the two image cells of AR after the call, carried to the machine's memory mem2 (below the shadow: U2 cannot touch
   them), as FSW_ret fsw_after_callU_args *)
destruct (fsw_got_shadow B lyc Sc W (unpoison U2 mem2) md2 Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U2 mem2)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B lyc Sc U2 W mem2 md2 (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U2 mem2)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) mem2) a 8 v).
{ intros a v Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U2 mem2) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U2 mem2) _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + exact (fsw_resume_frame_ok B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k _ f cs HJ HARU E2 Hfs Hcs).
  + (* the GOT word of the shadow base, as fsw_entryT *)
    unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + (* the shadow-base cell, as fsw_entryT *)
    unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
    rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
Lemma fsw_resume_after_rtU_args : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k
  regsT regs2 memT f xs cs rs gf r,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  aregs_preserved regsT regs2 ->
  spZ regsT = sp0 - f -> 0 < f -> f <= STK -> f mod 16 = 0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) memT) (sp0 - f)) cs ->
  (forall a, sp0 - f <= a < sp0 ->
     mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a) ->
  Forall (region_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W) mem2)) rs ->
  pairwise_disjoint (Ereg regs2 (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs2 (fs_extraT ++ xs)) gf ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regsT regs2 memT f xs cs rs gf r
  Hgot Hcell HJ HARU HP Hsp Hf Hfs Hal Hwf Hin Hcs Hkeep Hrs Hpd Hgf.
assert (Esp : getr regs2 2 = getr regsT 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs2 = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
exact (fsw_resume_after_rtU_args_chunks B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 f xs cs rs gf r
  Hgot Hcell HJ HARU Usp Hf Hfs Hal Hwf
  (fsw_chunks_kept _ _ memT mem2 (sp0 - f) 0 f cs Hin Hcs (fun a Ha => Hkeep a ltac:(lia))) Hrs Hpd Hgf).
Qed.

(* ---- the s0-anchored resume state at the return pc r, with extra regions: the window [sp0 + lo, sp0 + hi) at atom 8
   (s0 holds sp0 after the call: a caller that re-aligned sp keeps its saved words at literal offsets from s0) with the
   chunks cs, then the extra regions rs (each region_ok on the memory after the call, the walker's: a stack slot at the
   re-aligned sp by fsw_resume_stack_region_ok, a fake frame by its own presence and flag word); the facts are atom 8's
   (sp0, 16-aligned) then the extra atom facts gf. FSW_K's fss_ret_s0 r lo hi cs is fss_ret_s0_args r lo hi cs [] [] (by
   conversion). ---- *)
Definition fss_ret_s0_regs (lo hi : Z) (cs : list YP09.chunk) (rs : list YP09.region) : list YP09.region :=
  fs_ret_s0_region lo hi cs :: rs.
Definition fss_ret_s0_args (pc lo hi : Z) (cs : list YP09.chunk) (rs : list YP09.region) (gf : list (nat * afact))
  : sstate :=
  mkSS pc sr_atoms (fss_ret_s0_regs lo hi cs rs) None (mkFacts ((8%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: gf) [] []).
Lemma fsw_resume_after_rtU_s0_chunks : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2
  k regs2 extra cs rs gf r lo hi,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  YK11.getr regs2 8%bv = Z_to_bv 64 sp0 ->
  sp0 - STK <= sp0 + lo -> hi <= 0 ->
  regions_wf (fss_ret_s0_regs lo hi cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2) sp0) cs ->
  Forall (region_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2)) rs ->
  pairwise_disjoint (Ereg regs2 extra) (fss_ret_s0_regs lo hi cs rs) ->
  atoms_ok (Ereg regs2 extra) gf ->
  st_ok tfibsegs (Ereg regs2 extra) (fss_ret_s0_args r lo hi cs rs gf)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 extra cs rs gf r lo hi
  HJ HARU Hs0 Hwin Hhi0 Hwf Hcs Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (E8 : bv_unsigned (ew (Ereg regs2 extra) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs2 extra 8 8%bv eq_refl), Hs0; apply wz; lia).
rewrite restrict_mkst_fx. unfold fss_ret_s0_args. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- unfold fss_ret_s0_regs. constructor; [|exact Hrs]. unfold region_ok, fs_ret_s0_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E8. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable tfibsegs).
  apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1. cbn [af_lo af_hi af_al2]. rewrite E8.
  change (2 ^ 4) with 16. split; [|exact Hgf]. split; [lia | split; [exact Hal16 | lia]].
Qed.
Lemma fsw_resume_after_rtU_s0 : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k
  regs2 memT extra cs rs gf r lo hi,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  YK11.getr regs2 8%bv = Z_to_bv 64 sp0 ->
  sp0 - STK <= sp0 + lo -> lo <= hi -> hi <= 0 ->
  regions_wf (fss_ret_s0_regs lo hi cs rs) = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) memT) sp0) cs ->
  (forall a, sp0 + lo <= a < sp0 + hi ->
     mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) memT) a) ->
  Forall (region_ok tfibsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2)) rs ->
  pairwise_disjoint (Ereg regs2 extra) (fss_ret_s0_regs lo hi cs rs) ->
  atoms_ok (Ereg regs2 extra) gf ->
  st_ok tfibsegs (Ereg regs2 extra) (fss_ret_s0_args r lo hi cs rs gf)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 memT extra cs rs gf r lo hi
  HJ HARU Hs0 Hwin Hlohi Hhi0 Hwf Hin Hcs Hkeep Hrs Hpd Hgf.
exact (fsw_resume_after_rtU_s0_chunks B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 extra cs rs gf r lo
  hi HJ HARU Hs0 Hwin Hhi0 Hwf (fsw_chunks_kept _ _ memT mem2 sp0 lo hi cs Hin Hcs Hkeep) Hrs Hpd Hgf).
Qed.

(* a stack region with no chunks at atom n (worth b), window [lo, hi) inside the journal's stack window [sp0 - STK, sp0),
   on the memory after the call (its bytes present: the journal's window presence through ARU) *)
Lemma fsw_resume_stack_region_ok : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k
  E n b lo hi,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  bv_unsigned (ew E n) = b -> sp0 - STK <= b + lo -> lo <= hi -> b + hi <= sp0 ->
  region_ok tfibsegs E (mrestrict (w_H W) mem2) (YP09.mkRegion (Some n) lo hi lo hi []).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k E n b lo hi HJ HARU En Hlo Hlohi Hhi.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite En. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (apresent_writable tfibsegs).
apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
Qed.
End e.
