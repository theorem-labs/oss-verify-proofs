(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_parse_items_grow.v, with its module paths changed; 102 of its 168 lines of code are new or changed and 339 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/ZZwv_ret.v (a working branch
   1a5dc5b2e7c): same lemma names, statements and proofs; imports point at lib/B's image files and walk kit (YB1v, YB1w,
   FSH_Base, FSH_Rt, FSPstat, FSH_Fn_writer, FSW_K, FSW_K3, FSW_ret, FSW_rres); the image-agnostic FSupoison,
   FSupoisonU, FSH_YC20, FSH_Gen stay lib/A's.
   rule 24: proves no function (kind: segment lemma) - the container arms of write_value B.
   write_value's CONTAINER arms (fs.asan-ubsan image B, write_value 0x84010): the RESUME after a writer callee
   returns, with the frame top (write_value's entry sp, spF) BELOW the journal's window top (the spec's raised ot, sp0).
   KIT GAP, closed here: FSW_rres.fsw_resume_after_rtU_args_chunks and FSW_write_value_entry.wvc_after_call_ot place
   the resumed frame at sp0 - f, the journal's own top, so for a caller whose journal top is raised above its frame
   (FSH_Fn_FORM 3a: every WRITER callee and write_value itself) the frame they build is [spF - f, sp0), not
   write_value's [spF - 192, spF). The two lemmas below are those two with the frame top spF as its own parameter
   (sp0 - STK <= spF - f, spF <= sp0); their proofs are FSW_rres's (a Theorem Labs lane's kit) and wvc_after_call_ot's with that
   one change. Rule 24: no function proved here (write_value's lookup: lane record (internal path), CHECKER CONFIRM
   a Theorem Labs lane). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSW_K FSW_K3 FSW_ret FSW_rres.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance
   resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the frame region [spF - f, spF) on the memory after the call: inside the journal's window, so present *)
Lemma wvc_frame_ok2 : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2 md2 k E f cs spF,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  bv_unsigned (ew E 2) = spF - f -> 0 <= f -> sp0 - STK <= spF - f -> spF <= sp0 ->
  Forall (YP09.chunk_ok tfibsegs E (rdW W mem2) (spF - f)) cs ->
  region_ok tfibsegs E (rdW W mem2) (fstk_ret f cs).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k E f cs spF HJ HARU E2 Hf Hlo Hhi Hcs.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E2. split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable tfibsegs).
apply (fsw_apresent_unpoison B lyc Sc U2 W mem2 md2 _ HARU); [lia|]. apply Hpres. lia.
Qed.

(* fss_retT at the return pc r with the frame at spF - f (FSW_rres.fsw_resume_after_rtU_args_chunks, frame top split) *)
Lemma wvc_resume_args2 : forall B STK sp0 FP ly S W0 mem md own lyc Sc U2 (W : world tfibsegs) mem2
  md2 k regs2 f xs cs rs gf r spF,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U2 mem2) md2 k ->
  ARU tfibsegs B lyc Sc U2 W mem2 md2 ->
  spZ regs2 = spF - f -> 0 < f -> sp0 - STK <= spF - f -> spF <= sp0 -> f mod 16 = 0 -> spF mod 16 = 0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (rdW W mem2) (spF - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (rdW W mem2)) rs ->
  pairwise_disjoint (Ereg regs2 (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs2 (fs_extraT ++ xs)) gf ->
  st_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 r) mem2 (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k regs2 f xs cs rs gf r spF
  Hgot Hcell HJ HARU Usp Hf Hlo Hhi Hal HalF Hwf Hcs Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 2) = spF - f)
  by (rewrite (ew_Ereg_nat regs2 (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs2 (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
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
  + exact (wvc_frame_ok2 B STK sp0 FP ly S W0 mem md own lyc Sc U2 W mem2 md2 k _ f cs spF HJ HARU E2 ltac:(lia)
      Hlo Hhi Hcs).
  + unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + unfold fs_bcell_region, region_ok.
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
    rewrite Zminus_mod, HalF. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.

(* the after-call step of a caller whose journal top sp0 is above its frame top spF (FSW_write_value_entry.wvc_after_call_ot,
   frame top split): the outer journal grows by the callee's, ARU at the return, the resumed fss_retT *)
Lemma wvc_after_call2 : forall B STK sp0 FP own ly S U (W0 W : world tfibsegs) mem md lyc Sc Uc memC mdC k
    STKc FP1 ot f regsC ly' S' U' W' regs' mem' md' kc xs cs rs gf r spF,
  FsShadowSyms B ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B (STKc + (ot - spZ regsC)) ot FP1 lyc Sc W (unpoison Uc memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub B ly S lyc Sc own FP FP1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = spF - f -> 0 < f -> 0 <= STKc -> STKc + f + (sp0 - spF) <= STK -> f mod 16 = 0 -> spF mod 16 = 0 ->
  spZ regsC <= ot -> ot <= sp0 -> spF <= sp0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' mem') (spF - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' mem')) rs ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 FP own ly S U W0 W mem md lyc Sc Uc memC mdC k STKc FP1 ot f regsC ly' S' U' W' regs' mem' md' kc
  xs cs rs gf r spF HSS HJ HARU HJc HFP OK' PO' HP Hsp Hf HSc Hbud Hal HalF Hot1 Hot2 HspF Hwf Hcs Hrs Hpd Hgf.
destruct HSS as [HBgot HBcell].
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md ([] ++ own)
  ly' S' W' (unpoison U' mem') md' (k + kc)).
{ apply (fsw_ajournal_sub5 B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
    (STKc + (ot - spZ regsC)) ot FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc); [lia | lia | exact HFP]. }
cbn [app] in HJ2.
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (pose proof HJ2 as (HAR2 & _); split; [exact HAR2 | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
assert (Esp : spZ regs' = spF - f).
{ unfold spZ. rewrite (fsw_pres regsC regs' 2%bv HP ltac:(unfold acallee_saved; vm_compute; lia)). exact Hsp. }
exact (wvc_resume_args2 B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' U' W' mem' md' (k + kc)
  regs' f xs cs rs gf r spF HBgot HBcell HJ2 HARU' Esp Hf ltac:(lia) HspF Hal HalF Hwf Hcs Hrs Hpd Hgf).
Qed.

End R.
