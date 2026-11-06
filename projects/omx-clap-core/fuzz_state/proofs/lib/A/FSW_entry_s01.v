(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFl3.v:106-108
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:383-389, 448-454, 493-498, 501-509 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:625-631 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:208-214, 227-233 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg10.v, with its module paths and module names changed; 2634 of its 2686 lines of code are new or changed and 608 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSH_parse_value.v, with its addresses and numbers changed; 231 of its 326 lines of code are new or changed and 2591 lines of the source are left out. *)
(* fs program part, lane ENTRY, segments S0 + S1 (+ the dead S1') of the LLVMFuzzerTestOneInput walk (fs.asan
   0x80f1c-0x80f88, plan entry-walk-plan.md): fe_seg01, from the entry configuration to the resume after
   __asan_stack_malloc_0 (FSW_entry_defs.v ss_B2 / INV_B2), in the form fe_enter. rule 24: no function proved (fs's own
   harness entry, written in the donor cgif_file_fuzzer's form).
   - 0x80f1c-0x80f50: sp -= 96, `sd zero, 0(sp)`, the eleven saves at s0 - 8 .. s0 - 88, s0 := the entry sp;
   - 0x80f54-0x80f80: `andi sp, sp, -32` (sp = s1 = fe_sp1), s3 := a1, s4 := a0, s6 := the shadow base (GOT 0x9f6f0),
     a2 := the use-after-return flag (GOT 0x9f748 -> 0xa7f40, which holds 1 by AR_const_law at tl_got_uar /
     tl_uar_cell: FSW_K fsw_uar_regions_ok), so `beqz a2` (0x80f7c) is not taken;
   - 0x80f84: __asan_stack_malloc_0(64), ra 0x80f88: granted (frames S = [] at the entry, FSH_Fn_entry.fs_fake_granted),
     so the real-stack fallback S1' (0x80f90, 0x80f9c-0x80fb4) is dead and the walk resumes at 0x80f88 with a0 = the
     class-0 fake frame (FSW_frame.fsw_stack_malloc_atU, FSW_frame3.fsw_resume_after_stack_mallocU).
   The walk's footprint is the closed FS_PSTAT_FP, so the model step is same_io (YCbq.aos_step_closed_same_io); the
   statics' fs_stat is kept by the run (stack writes only, FSW_K fs_glob_below) and by the call (its image clause,
   acall_kept, given the statics are neither runtime-owned nor errno: fs_img_facts' first conjunct, IMG).
   Ported from: a working branch c4bfd3bc057 lib/A/FSH_check_reject_clean_starved.v crcs_ss0,
   crcs_ss1, crcs_entry, crcs_seg0, crcs_sm_site, crcs_glob_img, crcs_glob_keep (here at the 96-byte frame of the
   entry and FS_PSTAT_FP); the steps are FSW_K's (fsw_entryT_args, fsw_uar_regions_ok, fsw_aj_run_toU, fsw_realign_val)
   and FSW_frame's (fsw_stack_malloc_atU). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame FSW_frame3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
ACfn FSH_Harness FSH_Fn_entry FSW_entry_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_entry_link AF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- pure facts ---- *)
(* a chunk read under one env reads the same under another when its value denotes the same word *)
Lemma fe01_chunk_xfer : forall E E' (m : word -> option byte) base off (w : N) e e',
  sv_denot E e = sv_denot E' e' ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal w e)) ->
  YP09.chunk_ok tfibsegs E' m base (YP09.mkChunk off (CVal w e')).
Proof.
intros E E' m base off w e e' He H i Hi. destruct (H i Hi) as (b & H1 & H2). exists b. split; [|exact H2].
cbn [YP09.cbyte YP09.c_val YP09.c_off] in *. rewrite <- He. exact H1.
Qed.
(* fuzz/alloc.c's statics are image bytes (tfibsegs' last RW segment [0xa1000, 0x5fd000) holds .data and .bss) *)
Lemma fe01_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : 0xa1000 <= a < 0x5fd000).
{ unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; lia. }
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0xa1000) && (0x5fd000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. lia.
Qed.
(* fs_glob survives any memory change that keeps the bytes of FS_PSTAT_FP *)
Lemma fe01_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv k Hkk.
  rewrite (Hk (g + Z.of_nat k) (inFP_FS_PSTAT_FP g Hg (g + Z.of_nat k) ltac:(lia))). exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [vm_compute; repeat (first [left; reflexivity | right]) | exact G1]|].
split; [apply VB; [vm_compute; repeat (first [left; reflexivity | right]) | exact G2]|].
split; [apply VB; [vm_compute; repeat (first [left; reflexivity | right]) | exact G3]|].
split; [apply VB; [vm_compute; repeat (first [left; reflexivity | right]) | exact G4]|].
exact R.
Qed.
Lemma fe01_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof.
intros (r & Hr & H0). unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H0; lia.
Qed.

(* ================= the walk ================= *)
(* the entry state: fss0T (the shadow-base cells) with the use-after-return cells (FSW_K fs_uar_regions) and the
   0x60-byte frame of the prologue *)
Definition fe01_ss0 : sstate := fss0T_args A_LLVMF 96 fs_uar_regions [].
(* the state at the call of __asan_stack_malloc_0 (0x80f84 -> 0x3d484): MEASURED (vm_compute) sp = SAlu AND (SOff 2 (-96))
   (SLit (-32)), s1 = that + 0, s0 = the entry sp (atom 2), ra = 0x80f88, a0 = 64, a2 = 1 (the flag), s3 / s4 = the entry
   a1 / a0 (atoms 11 / 10), s6 = the shadow base atom 32; the frame [-96, 0) at atom 2 holds the eleven saves (s9 at -88
   .. ra at -8, each its entry atom) and 0 at -96 *)
Definition fe01_ss1 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs entry_tbl FUEL PC_stack_malloc_0 fe01_ss0).
Definition fe01_stk1 : YP09.region := Eval vm_compute in nth 0 (ss_mem fe01_ss1) (fstk 0).

(* a callee-saved register literal: acallee_saved of its number *)
Ltac fe01_cs :=
  unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis tl_got_shadow : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis tl_shadow_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Hypothesis tl_got_uar : as_got_uar B = fs_D_GOT_uar.
Hypothesis tl_uar_cell : as_uar_cell B = fs_D_uar_cell.
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the entry's own runtime use: FsEntryRt's stack_malloc_0, at the pc TfibLib's code table names *)
Hypothesis tl_code : as_code B = AF0l.Tfib_code.
Hypothesis fe_sm0 : astack_malloc_realizesU tfibsegs B 0.

Lemma fe01_entry_st : forall ly S U (W : world tfibsegs) regs mem md ch,
  afn_preU tfibsegs B LLVMF_STK ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) fe01_ss0
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_LLVMF) mem (YK11.seg_rom tfibsegs))).
Proof.
intros ly S U W regs mem md ch HPRE.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
apply (fsw_entryT_args B _ 96 ly S U W regs mem md ch _ fs_uar_regions [] tl_got_shadow tl_shadow_cell HPRE).
- unfold LLVMF_STK. lia.
- vm_compute. reflexivity.
- exact (fsw_uar_regions_ok B _ ly S U W regs mem md ch _ tl_got_uar tl_uar_cell HPRE).
- apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, fs_uar_regions, fs_got_uar_region, fs_uar_cell_region, fs_got_region,
    fs_bcell_region, fstk, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, fs_D_GOT_uar,
    fs_D_uar_cell.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold LLVMF_STK in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- exact I.
Qed.

(* segment S0 + S1: the prologue, the re-align and the flag test, up to the call of __asan_stack_malloc_0 *)
Lemma fe01_seg0 : forall ly S U (W : world tfibsegs) regs mem md ch FP (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B LLVMF_STK ly S U W regs mem md ch ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs fs_extraT) fe01_ss1 (restrict (w_H W) ms) ->
     ajournal tfibsegs B LLVMF_STK (spZ regs) FP ly S W (unpoison U mem) md [] ly S W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     frame_of (Ereg regs fs_extraT) (ss_mem fe01_ss0) mem (ms_mem ms) ->
     frame_of (Ereg regs fs_extraT) (ss_mem fe01_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP Q HPRE K.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
pose proof (fe01_entry_st ly S U W regs mem md ch HPRE) as HS.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
pose proof (ajournal_init tfibsegs B LLVMF_STK FP ly S W regs (unpoison U mem) md ch (proj1 HPRE)) as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_LLVMF) with (Z_to_bv 64 A_LLVMF).
fsw_aj_run_toU entry_tbl_ok HS HJ HARU PC_stack_malloc_0.
{ awr_ok_tac. exact Usp. }
exact (K _ _ HS HJ HARU HF HFr).
Qed.

(* the registers at the call of __asan_stack_malloc_0 (read off fe01_ss1): sp = s1 = the re-aligned sp1, a0 = 64
   (class 0), ra = 0x80f88, gp / tp kept, s0 = the entry sp, s3 / s4 = the entry a1 / a0, s6 = the shadow base,
   s10 / s11 kept *)
Lemma fe01_sm_site : forall ly S U (W : world tfibsegs) regs mem md ch ms,
  afn_preU tfibsegs B LLVMF_STK ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) fe01_ss1 (restrict (w_H W) ms) ->
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 96) / 32)) /\
  YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 96) / 32)) /\
  spZ regs - 112 <= 32 * ((spZ regs - 96) / 32) <= spZ regs - 96 /\ (32 * ((spZ regs - 96) / 32)) mod 16 = 0 /\
  YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x80f88 /\ YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 64 /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv /\
  YK11.getr (ms_regs ms) 8%bv = YK11.getr regs 2%bv /\ YK11.getr (ms_regs ms) 22%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 19%bv = YK11.getr regs 11%bv /\ YK11.getr (ms_regs ms) 20%bv = YK11.getr regs 10%bv /\
  YK11.getr (ms_regs ms) 26%bv = YK11.getr regs 26%bv /\ YK11.getr (ms_regs ms) 27%bv = YK11.getr regs 27%bv.
Proof.
intros ly S U W regs mem md ch ms HPRE HS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
set (E := Ereg regs fs_extraT) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
  unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (fsw_realign_facts (spZ regs - 96) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
set (sp1 := 32 * ((spZ regs - 96) / 32)) in *.
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1).
{ exact (fsw_realign_val E fe01_ss1 (restrict (w_H W) ms) 2%bv 2 (-96) (spZ regs) HS
    ltac:(vm_compute; reflexivity) E2 ltac:(unfold spZ; apply u64_range) ltac:(lia)). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E fe01_ss1 ms 9%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 ?v => change (sr_get (ss_regs fe01_ss1) 9%bv) with
    (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32))) (SLit 0)) end.
  rewrite denot_lit_U, U_SAlu. f_equal. cbn [zalu_raw]. rewrite U_SLit.
  assert (UA : YP0e.U E (SAlu ALU_AND (SOff 2 (-96)) (SLit (-32))) = sp1).
  { unfold YP0e.U. rewrite (denot_and_m32 E 2 (spZ regs) (-96) E2 ltac:(lia) ltac:(lia) ltac:(unfold spZ; apply u64_range)).
    apply wz. lia. }
  rewrite UA. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
split; [exact R2|]. split; [exact R9|]. split; [lia|]. split; [exact F3|].
split; [exact (fsw_reg_lit _ E _ ms 1%bv 0x80f88 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 10%bv 64 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E fe01_ss1 ms 22%bv HS).
  change (sr_get (ss_regs fe01_ss1) 22%bv) with (SOff 32 0). rewrite fsw_SOff0.
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 19%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 20%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 26%bv 26%bv 26 HS ltac:(vm_compute; reflexivity) eq_refl)|].
exact (fsw_reg_atom _ regs fs_extraT _ ms 27%bv 27%bv 27 HS ltac:(vm_compute; reflexivity) eq_refl).
Qed.

(* the eleven saved words at the call, read off fe01_ss1's frame region, as fe_sv_chunks under any env carrying
   fe_extra (atom 33 + k is the k-th saved register of the entry) *)
Lemma fe01_sv_ok : forall cx (W : world tfibsegs) ms regs2,
  st_ok tfibsegs (Ereg (c_regs cx) fs_extraT) fe01_ss1 (restrict (w_H W) ms) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fe_extra cx)) (mrestrict (w_H W) (ms_mem ms)) (fe_sp0 cx)) fe_sv_chunks.
Proof.
intros cx W ms regs2 HS.
set (E0 := Ereg (c_regs cx) fs_extraT) in *.
pose proof (fsw_region_nth E0 fe01_ss1 (restrict (w_H W) ms) 0 fe01_stk1 HS ltac:(vm_compute; reflexivity)) as HR.
destruct HR as (_ & _ & _ & HC).
assert (EB : base_val E0 (YP09.r_base fe01_stk1) = fe_sp0 cx).
{ change (YP09.r_base fe01_stk1) with (Some 2%nat). cbn [base_val]. subst E0.
  rewrite (ew_Ereg_nat (c_regs cx) fs_extraT 2 2%bv eq_refl). reflexivity. }
rewrite EB in HC. cbn [ms_mem restrict] in HC.
pose proof (proj1 (Forall_forall _ _) HC) as HCi.
assert (X : forall off n (r : bv 5) j, Z.of_nat n = bv_unsigned r ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks fe01_stk1) ->
  nth j (fe_extra cx) (Z_to_bv 64 0) = YK11.getr (c_regs cx) r ->
  YP09.chunk_ok tfibsegs (Ereg regs2 (fe_extra cx)) (mrestrict (w_H W) (ms_mem ms)) (fe_sp0 cx)
    (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off n r j Hnr Hin Hn.
  apply (fe01_chunk_xfer E0 _ _ _ off 8 (SOff n 0)); [|exact (HCi _ Hin)].
  rewrite fsw_extra_atom, Hn, fsw_SOff0. subst E0. apply ew_Ereg_nat. exact Hnr. }
apply Forall_forall. intros c Hc. unfold fe_sv_chunks in Hc. cbn [map seq In] in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
  [ apply (X (-8) 1%nat 1%bv 1%nat) | apply (X (-16) 8%nat 8%bv 2%nat) | apply (X (-24) 9%nat 9%bv 3%nat)
  | apply (X (-32) 18%nat 18%bv 4%nat) | apply (X (-40) 19%nat 19%bv 5%nat) | apply (X (-48) 20%nat 20%bv 6%nat)
  | apply (X (-56) 21%nat 21%bv 7%nat) | apply (X (-64) 22%nat 22%bv 8%nat) | apply (X (-72) 23%nat 23%bv 9%nat)
  | apply (X (-80) 24%nat 24%bv 10%nat) | apply (X (-88) 25%nat 25%bv 11%nat) ];
  first [reflexivity | vm_compute; repeat (first [left; reflexivity | right])].
Qed.

(* ---- segments S0 + S1 + the dead S1': from the entry to the resume after __asan_stack_malloc_0 (B2) ---- *)
Lemma fe_seg01 : forall POST, fe_enter B FS_PSTAT_FP POST ss_B2 (INV_B2 B).
Proof.
intros POST ly S W regs mem md p n pl M live cnt HB HF.
pose proof (HB 0) as (HPx & HST & _).
cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M c_live c_cnt c_fpos] in HPx, HST.
pose proof HPx as (HAP & _ & _ & _ & Hpn & _ & _ & Hfr & _).
pose proof HAP as (HAR & _ & _ & Hgp & Htp & _).
pose proof (fsw_preU_nil B LLVMF_STK ly S W regs mem md [] HAP) as HPRE.
pose proof (fsw_sp B _ ly S [] W regs mem md [] HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
apply (fe01_seg0 ly S [] W regs mem md [] FS_PSTAT_FP _ HPRE).
intros ms mat HS HJ HARU HFr0 _.
change (unpoison [] mem) with mem in HJ.
set (mdc := with_vm_backing (m_vm_lazy md) mat md) in *.
destruct (fe01_sm_site ly S [] W regs mem md [] ms HPRE HS)
  as (R2 & R9 & Hsp1 & Hsp16 & R1 & R10 & R3 & R4 & R8 & R22 & R19 & R20 & R26 & R27).
set (sp1 := 32 * ((spZ regs - 96) / 32)) in *.
(* the statics at the call: the run wrote only its stack frame *)
assert (SB : same_below mem (ms_mem ms) alloc_ceiling).
{ intros x Hx. apply HFr0. intros (r & Hr & Hlo).
  rewrite (wz x ltac:(lia)) in Hlo.
  unfold fe01_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_uar_regions in Hr. cbn [ss_mem app In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [fstk fs_got_region fs_bcell_region fs_got_uar_region fs_uar_cell_region YP09.r_base YP09.r_wlo YP09.r_whi
      base_val] in Hlo; [|lia..].
  rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl) in Hlo.
  change (bv_unsigned (YK11.getr regs 2%bv)) with (spZ regs) in Hlo. unfold LLVMF_STK in Hceil. lia. }
(* the call *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ fe01_ss1 ms HS eq_refl).
change (ss_pc fe01_ss1) with PC_stack_malloc_0.
assert (EPC : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0) by (rewrite tl_code; reflexivity).
pose proof fe_sm0 as ASM.
rewrite <- EPC.
assert (Hsp' : spZ (ms_regs ms) = spZ regs + (sp1 - spZ regs))
  by (change (spZ (ms_regs ms)) with (bv_unsigned (YK11.getr (ms_regs ms) 2%bv)); rewrite R2, wz; lia).
assert (Hmod : (sp1 - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, Hal16, Hsp16; reflexivity).
assert (Hgrant : count_cid 0 (frames S) < fs_frames 0).
{ rewrite Hfr. apply fs_fake_granted; [lia | cbn [length Z.of_nat]; unfold FRL_MAX; lia]. }
eapply SRr_bind.
{ exact (fsw_stack_malloc_atU B errno_low ML (FSW_entry_link.fe_stack_malloc_progress B) 0 ASM ltac:(lia)
    W (ms_regs ms) (ms_mem ms) LLVMF_STK (spZ regs) FS_PSTAT_FP ly S W mem md [] ly S [] mdc 0
    (sp1 - spZ regs) (Z_to_bv 64 0x80f88) HJ HARU Hsp' Hmod ltac:(lia) ltac:(unfold ESTACK, LLVMF_STK; lia)
    ltac:(rewrite R3; exact Hgp) ltac:(rewrite R4; exact Htp) R1 ltac:(apply ret_ok_even; vm_compute; reflexivity) Hgrant). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HARU2 & HP & HR10 & Eab & Efr & _ & Enev & Ebb
  & Hz & Hflag & Hkept).
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hkept by lia.
pose proof Hkept as (_ & _ & K3 & _). rewrite !unpoison_nil in K3.
pose proof HJ2 as (_ & _ & _ & _ & Hio & _ & _ & _ & _ & F2 & _). rewrite !unpoison_nil in F2.
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Efr; left; reflexivity).
pose proof (ARU_AR tfibsegs B ly S2 [] W mem2 md2 HARU2) as HAR2.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison [] mem2) md2 0 pos HAR2 Hin2) as (HF4096 & HFc & _).
change (fs_frame_bytes 0) with 64 in HFc.
(* the statics after the call: image bytes, not runtime-owned and not errno (IMG's first conjunct) *)
assert (HST2 : fs_stat tfibsegs W mem2 live cnt).
{ destruct HST as (peak & HG). exists peak.
  apply (fe01_glob_keep W (ms_mem ms) mem2 live peak cnt SIZE_MAXZ).
  - intros a Ha. apply (mbyte_of_aview tfibsegs (w_H W) (w_H W) (ms_mem ms) mem2 a).
    apply K3; [exact (fe01_pstat_img a Ha) | exact (proj1 (proj1 IMG a Ha)) | exact (proj2 (proj1 IMG a Ha))].
  - exact (fs_glob_below W mem (ms_mem ms) live peak cnt SIZE_MAXZ SB HG). }
(* the callee-saved registers after the call are the call site's *)
assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr (ms_regs ms) r)
  by (intros r Hr; exact (fsw_pres _ _ r HP Hr)).
assert (G8 : YK11.getr regs2 8%bv = YK11.getr regs 2%bv) by (rewrite P; [exact R8 | fe01_cs]).
assert (G9 : YK11.getr regs2 9%bv = Z_to_bv 64 sp1) by (rewrite P; [exact R9 | fe01_cs]).
assert (G2 : YK11.getr regs2 2%bv = Z_to_bv 64 sp1) by (rewrite P; [exact R2 | fe01_cs]).
assert (G3 : YK11.getr regs2 3%bv = YK11.getr regs 3%bv) by (rewrite P; [exact R3 | fe01_cs]).
assert (G4 : YK11.getr regs2 4%bv = YK11.getr regs 4%bv) by (rewrite P; [exact R4 | fe01_cs]).
assert (G19 : YK11.getr regs2 19%bv = YK11.getr regs 11%bv) by (rewrite P; [exact R19 | fe01_cs]).
assert (G20 : YK11.getr regs2 20%bv = YK11.getr regs 10%bv) by (rewrite P; [exact R20 | fe01_cs]).
assert (G22 : YK11.getr regs2 22%bv = Z_to_bv 64 SHADOW_OFF) by (rewrite P; [exact R22 | fe01_cs]).
assert (G26 : YK11.getr regs2 26%bv = YK11.getr regs 26%bv) by (rewrite P; [exact R26 | fe01_cs]).
assert (G27 : YK11.getr regs2 27%bv = YK11.getr regs 27%bv) by (rewrite P; [exact R27 | fe01_cs]).
set (cx := mkFECX ly S W regs mem md p n pl M live cnt pos).
set (E := Ereg regs2 (fe_extra cx)).
assert (EW : forall (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = YK11.getr regs2 r)
  by (intros k r Hk; exact (ew_Ereg_nat regs2 (fe_extra cx) k r Hk)).
eapply SRr_mono.
{ apply (HF cx E 0 ly S2 [] W (YK11.mkst regs2 (Z_to_bv 64 RA_stack_malloc) mem2 (YK11.seg_rom tfibsegs)) md2).
  - exact (HB pos).
  - intros j Hj. apply ew_Ereg_extra.
  - exact HJ2.
  - exact HARU2.
  - (* INV_B2 *)
    split; [reflexivity|]. split; [reflexivity|]. split; [exact Eab|]. split; [exact Enev|]. split; [exact Ebb|].
    split; [exact (aos_step_closed_same_io FS_PSTAT_FP md md2 fe01_closed Hio)|].
    split; [rewrite (EW 8%nat 8%bv eq_refl), G8; unfold fe_sp0, spZ; cbn [c_regs]; symmetry; apply Z_to_bv_bv_unsigned|].
    split; [rewrite (EW 9%nat 9%bv eq_refl), G9; reflexivity|].
    split; [rewrite (EW 2%nat 2%bv eq_refl), G2; reflexivity|].
    split; [rewrite (EW 10%nat 10%bv eq_refl), HR10; reflexivity|].
    split; [rewrite (EW 19%nat 19%bv eq_refl), G19; reflexivity|].
    split; [rewrite (EW 20%nat 20%bv eq_refl), G20; reflexivity|].
    split; [rewrite (EW 22%nat 22%bv eq_refl), G22; reflexivity|].
    split; [rewrite (EW 3%nat 3%bv eq_refl), G3; reflexivity|].
    split; [rewrite (EW 4%nat 4%bv eq_refl), G4; reflexivity|].
    split; [rewrite (EW 26%nat 26%bv eq_refl), G26; reflexivity|].
    split; [rewrite (EW 27%nat 27%bv eq_refl), G27; reflexivity|].
    split; [exact Hz|].
    split; [|exact HST2].
    change (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem2 (p + i) = aview tfibsegs (w_H W) mem (p + i)).
    intros i Hi.
    destruct Hpn as [(-> & _) | (_ & Hin)]; [lia|].
    pose proof (req_size_pos n ltac:(lia)) as (_ & Hrq).
    apply (F2 p n i Hin ltac:(rewrite Eab; exact Hin) ltac:(lia)).
    intros Hf. apply (blk_img tfibsegs B LAWS ly S W mem md p n (p + i) HAR Hin ltac:(lia)).
    exact (fe01_pstat_img _ Hf).
  - (* the resume state *)
    exact (FSW_frame3.fsw_resume_after_stack_mallocU B LLVMF_STK (spZ regs) FS_PSTAT_FP ly S W mem md [] ly S S2 []
      W (ms_mem ms) mdc mem2 md2 0 0 pos sp1 regs2 (fe_extra cx) RA_stack_malloc (-88) 0 fe_sv_chunks 9%nat 0 8 10%nat
      (SOff 44 0)
      HJ2 HARU2 HARU Hkept Hin2 ltac:(lia)
      ltac:(rewrite (ew_Ereg_nat regs2 (fe_extra cx) 8 8%bv eq_refl), G8; reflexivity)
      ltac:(rewrite (ew_Ereg_nat regs2 (fe_extra cx) 9 9%bv eq_refl), G9; apply wz; lia)
      ltac:(rewrite (ew_Ereg_nat regs2 (fe_extra cx) 10 10%bv eq_refl), HR10; apply wz; lia)
      ltac:(rewrite fsw_SOff0; change 44%nat with (32 + 12)%nat; rewrite ew_Ereg_extra; reflexivity)
      Hflag ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold LLVMF_STK; lia)
      ltac:(vm_compute; reflexivity)
      ltac:(unfold fe_sv_chunks; cbn [map seq]; repeat constructor; cbn; lia)
      (fe01_sv_ok cx W ms regs2 HS)). }
cbv beta. intros W' c' _ HP'. exists pos. exact HP'.
Qed.
End W.
