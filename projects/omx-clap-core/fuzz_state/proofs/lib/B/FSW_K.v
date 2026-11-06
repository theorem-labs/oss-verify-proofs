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
(* The walk kit for fs's ASan program part over fs.asan-ubsan (image tfibsegs): the image facts the donor engine (YCbq.v
   aj_run / SRr_run_AJ) asks for, the entry symbolic state of a function with a stack frame, the frame transfers below
   alloc_ceiling, register and frame reads of the symbolic state, the state after one program call, and the run / return
   tactics. A kit: no function's contract is proved here (rule 24).
   Ported from: a Theorem Labs lane's proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_K.v (a working branch 6fb011b3936). Changed:
   module path fuzz_manifest -> fuzz_state; fm -> fs names (fm_segs_low -> fs_segs_low, fm_wx -> fs_wx, fmw_* -> fsw_*,
   fm_glob_below -> fs_glob_below over FSH_Base.fs_glob, FM_RLO / FM_RHI -> FS_RLO / FS_RHI); YC20 -> FSH_YC20 (its
   arodata_okP / apost_base); cstr_ok_below over FSH_Gen.cstr_ok (S0 7dd4849273a text, the same clauses as a Theorem Labs lane's
   cstr_ok). Added for fs's U form (FSH_Gen.v afn_preU: afn_pre over the memory with the user-poisoned
   shadow bytes of U read as 0): fsw_sp / fsw_entry take afn_preU and read the entry state on the machine's own memory,
   fsw_sp_pre / fsw_entry_pre are the afn_pre corollaries (U = []); fsw_after_callU is fsw_after_call over journals of
   the unpoisoned memories with the resumed state read on the machine's own memory; fsw_run_AJU / fsw_run_to_AJU /
   fsw_run_tok_AJU / fsw_run_to_tok_AJU (tactics fsw_aj_runU / fsw_aj_run_toU / fsw_aj_run_tokU / fsw_aj_run_to_tokU)
   are the engine's runs with the symbolic state on the machine's memory, the journal over the unpoisoned memory, and
   ARU kept; fsw_ajournal_init_ot starts a journal at a window top ot above the entry sp (FSH_Fn_FORM.md 3a);
   fs_segs_img bounds the image by FSH_Base.FS_IMG_END.
   Over RELOC's core (a working branch 4b90d538804, a Theorem Labs lane 4c30cd807c4's awr_byte text): awr_byte and
   awr_ok take tfibsegs and B, and fr0 (the frames of the journal's entry state, frames S) after own; awr_byte is
   awr_byte0 (the donor's four cases) or an FP image byte that is no owned static or an FP byte of a frame of fr0.
   fsw_dest_okU takes awr_byte0, as YCbq.v awr_byte_present and aj_intrin_at do (an image byte need not be present);
   fsw_intrin_atU, fsw_ajournal_writeU, fsw_exec_U and the U run twins take awr_byte / awr_ok at (tfibsegs, B, frames S).
   KIT RULES (every walk lane):
   (R1) After an eapply, no positional tactic list `[t1 | t2 | ...]`: a premise the core adds changes the goal count
        and moves every tactic to the wrong goal. Discharge per goal, one solve per premise kind:
        `all: first [ solve [t1] | solve [t2] | ... ]` (in a tactic chain: `eapply X; first [ solve [t1] | ... ]`);
        a goal the walk keeps open is selected by its head (`lazymatch goal with |- awr_ok _ ... => ... end`). A bare
        `first` without `solve` can close the wrong goal. Guard every computing alternative by the goal's shape
        (`lazymatch goal with |- regions_wf _ = true => solve [vm_compute; reflexivity] end`); never a bare vm_compute
        or cbn in a `first` list: tried on a `Forall (chunk_ok tfibsegs ...)` goal it normalizes the image (ALLOC
        measured 30+ min).
   (R2) A writable rs region on an image static (fss0TS's statics) is written through awr_byte's static arm
        (inFP FP a /\ in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B)): every run over such a region needs
        FS_PSTAT_FP in its FP; the not-owned half is FSH_Gen.fs_pstat_not_owned (from FSH_Rt.fs_img_facts).
   (R3) An argument-object atom passed to fss0T_args / fsw_entryT_args carries `mkAF (2 ^ 46) (2 ^ 47 - n) 3`
        (n = the object size), not `mkAF (2 ^ 46) (2 ^ 47) 3`: YCbn.v:120-127 shent_in_span asks the shadow of
        [hi, hi + n) to end inside fs_Bspan, which needs hi + n <= 2 ^ 47. Discharge it from o + n <= ot <= ly_top ly
        <= 2 ^ 47 (o the object's address). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base FSH_Rt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- fs's image ---- *)
(* every loaded byte of fs.asan-ubsan lies below FS_IMG_END (FSH_Base.v: the last RW PT_LOAD's end, page-rounded) *)
Lemma fs_segs_img : forall a, in_img tfibsegs a -> 0 <= a < FS_IMG_END.
Proof.
intros a (sg & Hin & Hr).
assert (Hb : forallb (fun s => (0 <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? FS_IMG_END))
  tfibsegs = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb sg Hin) as H. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.
(* the form the engine's Section hypothesis segs_low takes (YCbq.v) *)
Lemma fs_segs_low : forall a, in_img tfibsegs a -> 0 <= a < kLowMemEnd.
Proof. intros a Ha. pose proof (fs_segs_img a Ha) as H. unfold FS_IMG_END, kLowMemEnd in *. lia. Qed.
Lemma fs_wx : wx_segs_nowrap tfibsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* ---- the entry state of a function whose prologue is `addi sp, sp, -f` ---- *)
Definition fstk (f : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- f) 0 (- f) 0 [].
Definition fss0 (pc f : Z) : sstate :=
  mkSS pc sr_atoms [fstk f] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* ---- U form: a byte at or above kHighMemBeg (the stack) is no user-poisoned shadow byte ---- *)
Lemma fsw_ARU : forall B STK ly S U (W : world tfibsegs) regs mem md ch,
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> ARU tfibsegs B ly S U W mem md.
Proof.
intros B STK ly S U W regs mem md ch (HAP & OK & PO). split; [exact (proj1 HAP)|]. split; [exact OK | exact PO].
Qed.
Lemma fsw_unpoison_high : forall B ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= a < 2 ^ 64 ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros B ly S U W mem md a H Ha. pose proof asan_consts as (_ & _ & C3 & _). pose proof (AR_laws_ok tfibsegs B) as LAWS.
apply unpoison_out. rewrite (wz a ltac:(lia)).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
assert (UF : aowned B ly S a /\ SHADOW_OFF <= a < kHighMemBeg) by (eapply ush_facts; eassumption). lia.
Qed.
Lemma fsw_aview_unpoison_high : forall B ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros B ly S U W mem md a H Ha. apply (aview_at tfibsegs). exact (fsw_unpoison_high B ly S U W mem md a H Ha).
Qed.
Lemma fsw_apresent_unpoison : forall B ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= a < 2 ^ 64 ->
  apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) mem a.
Proof.
intros B ly S U W mem md a H Ha (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite <- (fsw_unpoison_high B ly S U W mem md a H Ha). exact Hb.
Qed.
(* afn_pre is afn_preU at U = [] *)
Lemma fsw_preU_nil : forall B STK ly S (W : world tfibsegs) regs mem md ch,
  afn_pre tfibsegs B STK ly S W regs mem md ch -> afn_preU tfibsegs B STK ly S [] W regs mem md ch.
Proof.
intros B STK ly S W regs mem md ch H. split; [exact H|]. split; [split; [constructor | exact I]|]. intros s Hs. discriminate Hs.
Qed.

Lemma fsw_sp : forall B STK ly S U (W : world tfibsegs) regs mem md ch,
  afn_preU tfibsegs B STK ly S U W regs mem md ch ->
  spZ regs mod 16 = 0 /\ alloc_ceiling + STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ 0 <= STK.
Proof.
intros B STK ly S U W regs mem md ch (HPRE & _ & _).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2). lia.
Qed.
Lemma fsw_sp_pre : forall B STK ly S (W : world tfibsegs) regs mem md ch,
  afn_pre tfibsegs B STK ly S W regs mem md ch ->
  spZ regs mod 16 = 0 /\ alloc_ceiling + STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ 0 <= STK.
Proof.
intros B STK ly S W regs mem md ch HPRE. exact (fsw_sp B STK ly S [] W regs mem md ch (fsw_preU_nil _ _ _ _ _ _ _ _ _ HPRE)).
Qed.
(* the entry symbolic state, read on the machine's own memory mem (the stack window is no user-poisoned shadow) *)
Lemma fsw_entry : forall B STK f ly S U (W : world tfibsegs) regs mem md ch pc,
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> 0 <= f <= STK -> regions_wf [fstk f] = true ->
  st_ok tfibsegs (Ereg regs []) (fss0 pc f) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros B STK f ly S U W regs mem md ch pc HPRE Hf Hwf.
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPRE) as HARU.
pose proof HPRE as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
rewrite restrict_mkst_fx.
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold fss0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor].
  apply (region_ok_stack tfibsegs _ _ 2 (spZ regs) (- f) E2); [lia | lia |].
  intros a Ha. apply (apresent_writable tfibsegs).
  apply (fsw_apresent_unpoison B ly S U W mem md a HARU); [lia|]. apply Hpres. lia.
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal16 | lia]].
Qed.
Lemma fsw_entry_pre : forall B STK f ly S (W : world tfibsegs) regs mem md ch pc,
  afn_pre tfibsegs B STK ly S W regs mem md ch -> 0 <= f <= STK -> regions_wf [fstk f] = true ->
  st_ok tfibsegs (Ereg regs []) (fss0 pc f) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros B STK f ly S W regs mem md ch pc HPRE.
exact (fsw_entry B STK f ly S [] W regs mem md ch pc (fsw_preU_nil _ _ _ _ _ _ _ _ _ HPRE)).
Qed.

Lemma fsw_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. apply zcanon_id. unfold M64. apply u64_range.
Qed.
(* ---- the entry state of an INSTRUMENTED function: near its entry every instrumented function loads the ASan shadow
   base through the GOT, and the engine stops at that load (SR_load None) unless the two cells are in the symbolic
   state: the GOT word B/YB1w.v tfib_D_GOT_asan_shadow_memory_dynamic_address (0x9fc10) holds
   B/YB1w.v tfib_D_asan_shadow_memory_dynamic_address (0xa8438), which holds SHADOW_OFF. fss0T is fss0 with the two
   cells as regions and the shadow base as the extra atom 32 (the donor's shape, cgif A/ACeg.v:134-137 got_region /
   bcell_region, A/ACes.v:38-41 ss_rd / rd_extra); both cells come from AR (AR_const_law, Reusable/YG0d.v:460-466) at
   B's own cells, so the two cell equations of B are premises (the donor's TfibLib gives them: tl_got_shadow /
   tl_shadow_cell; fs's A/ACeg.v cannot be imported here, A/ACej.v does not compile). ---- *)
Definition fs_got_region : YP09.region :=
  YP09.mkRegion None tfib_D_GOT_asan_shadow_memory_dynamic_address (tfib_D_GOT_asan_shadow_memory_dynamic_address + 8) 0 0
    [YP09.mkChunk tfib_D_GOT_asan_shadow_memory_dynamic_address (CVal 8 (SLit tfib_D_asan_shadow_memory_dynamic_address))].
Definition fs_bcell_region (bx : nat) : YP09.region :=
  YP09.mkRegion None tfib_D_asan_shadow_memory_dynamic_address (tfib_D_asan_shadow_memory_dynamic_address + 8) 0 0
    [YP09.mkChunk tfib_D_asan_shadow_memory_dynamic_address (CVal 8 (SOff bx 0))].
Definition fsT_regions (f : Z) : list YP09.region := [fstk f; fs_got_region; fs_bcell_region 32].
Definition fss0T (pc f : Z) : sstate :=
  mkSS pc sr_atoms (fsT_regions f) None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
(* the entry env's extra atoms: atom 32 is the shadow base *)
Definition fs_extraT : list word := [Z_to_bv 64 SHADOW_OFF].
Lemma fsw_got_shadow : forall B ly S (W : world tfibsegs) mem md,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  AR tfibsegs B ly S W mem md ->
  rdword (aview tfibsegs (w_H W) mem) tfib_D_GOT_asan_shadow_memory_dynamic_address
    = Some tfib_D_asan_shadow_memory_dynamic_address /\
  rdword (aview tfibsegs (w_H W) mem) tfib_D_asan_shadow_memory_dynamic_address = Some SHADOW_OFF.
Proof.
intros B ly S W mem md Hgot Hcell HAR.
destruct (al_const tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite Hgot, Hcell in Kgot. rewrite Hcell in Kcell.
split; [exact Kgot | exact Kcell].
Qed.
Lemma fsw_entryT : forall B STK f ly S U (W : world tfibsegs) regs mem md ch pc,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> 0 <= f <= STK ->
  regions_wf (fsT_regions f) = true ->
  st_ok tfibsegs (Ereg regs fs_extraT) (fss0T pc f)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros B STK f ly S U W regs mem md ch pc Hgot Hcell HPRE Hf Hwf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPRE) as HARU.
pose proof HPRE as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
(* the two image cells of AR, carried to the machine's own memory (they are below the shadow, so U cannot touch them) *)
destruct (fsw_got_shadow B ly S W (unpoison U mem) md Hgot Hcell HAR) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U mem)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) mem) a 8 v).
{ intros a v Ha Hb Hv k Hk. rewrite (MB (a + Z.of_nat k) ltac:(lia)). exact (Hv k Hk). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U mem) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U mem) _ _ Kcell)]. }
rewrite restrict_mkst_fx. unfold fss0T, fsT_regions.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (E32 : ew (Ereg regs fs_extraT) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs fs_extraT) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (region_ok_stack tfibsegs _ _ 2 (spZ regs) (- f) E2); [lia | lia |].
    intros a Ha. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly S U W mem md a HARU); [lia|]. apply Hpres. lia.
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
- apply pairwise_disjoint_of_extents.
  unfold fs_got_region, fs_bcell_region, fstk, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. change (2 ^ 4) with 16. rewrite Z.pow_0_r.
  split; [split; [lia | split; [exact Hal16 | lia]]|].
  split; [|exact I]. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
(* the extra regions the walk of an instrumented function with POINTER ARGUMENTS or a fake frame needs besides the two
   shadow-base cells: fss0T_args appends them and takes their atom facts. The inline shadow checks of such an object
   are not regions: they are the token run's business (fsw_run_tok_AJU / fsw_aj_run_tokU with Bx := fs_Bx, the shadow
   base atom of fss0T, Bspan := fs_Bspan and one shent per object; the donor's A/ACes.v:28-29 RBx / RBspan). *)
Definition fs_Bx : sv := SOff 32 0.
Definition fs_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition fsT_regions_args (f : Z) (rs : list YP09.region) : list YP09.region := fsT_regions f ++ rs.
Definition fss0T_args (pc f : Z) (rs : list YP09.region) (gf : list (nat * afact)) : sstate :=
  mkSS pc sr_atoms (fsT_regions_args f rs) None
    (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: gf) [] []).
(* ---- ATOM CONVENTION (every lane). In every state: atom 2 = the entry sp, atom 8 = s0 (fss_ret_s0).
   NON-T states (fss0, fss_ret, fss_ret_s0: an uninstrumented wrapper, which loads no shadow base) have no reserved
   extra atom: the walk's extras start at atom 32, i.e. the env is Ereg regs extra with extra the walk's own list.
   T states (fss0T, fss0T_args, and the after-call T twins) reserve atom 32 for the shadow base (fs_extraT's only
   entry) and put the walk's own from atom 33 on, in the order of xs: xatom i is the atom of xs's i-th entry under
   the env Ereg regs (fs_extraT ++ xs). A walk that carries both the alloc.c statics and an object's fields puts
   xs := statics ++ fields (statics at xatom 0..3, the fields from xatom 4); an after-call state's saved-register
   chunks take the atoms after the walk's xs. The after-call steps (fsw_after_callU, fsw_after_callU_s0) are generic
   in the resumed env's extra list, so they serve both forms. ---- *)
Definition xatom (i : nat) : nat := 33 + i.
(* the three regions of fss0T, under an entry env whose extra atoms are fs_extraT ++ xs *)
Lemma fsw_T_regions_okX : forall B STK f ly S U (W : world tfibsegs) regs mem md ch xs,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> 0 <= f <= STK ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) (mrestrict (w_H W) mem)) (fsT_regions f).
Proof.
intros B STK f ly S U W regs mem md ch xs Hgot Hcell HPRE Hf.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPRE) as HARU.
pose proof HPRE as (HAP & _ & _).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (fsw_got_shadow B ly S W (unpoison U mem) md Hgot Hcell HAR) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U mem)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) mem) a 8 v).
{ intros a v Ha Hb Hv k Hk. rewrite (MB (a + Z.of_nat k) ltac:(lia)). exact (Hv k Hk). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U mem) _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U mem) _ _ Kcell)]. }
assert (E2 : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs (fs_extraT ++ xs) 2 2%bv eq_refl); reflexivity).
assert (E32 : ew (Ereg regs (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
unfold fsT_regions. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (region_ok_stack tfibsegs _ _ 2 (spZ regs) (- f) E2); [lia | lia |].
  intros a Ha. apply (apresent_writable tfibsegs).
  apply (fsw_apresent_unpoison B ly S U W mem md a HARU); [lia|]. apply Hpres. lia.
- unfold fs_got_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
  split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
    (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
    [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
- unfold fs_bcell_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
  split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
    [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
Qed.
Lemma fsw_T_regions_ok : forall B STK f ly S U (W : world tfibsegs) regs mem md ch,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> 0 <= f <= STK ->
  Forall (region_ok tfibsegs (Ereg regs fs_extraT) (mrestrict (w_H W) mem)) (fsT_regions f).
Proof.
intros B STK f ly S U W regs mem md ch Hgot Hcell HPRE Hf.
exact (fsw_T_regions_okX B STK f ly S U W regs mem md ch [] Hgot Hcell HPRE Hf).
Qed.
(* the entry state with extra regions rs, extra env atoms xs (xatom 0 on) and extra atom facts gf *)
Lemma fsw_entryT_argsX : forall B STK f ly S U (W : world tfibsegs) regs mem md ch pc rs gf xs,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> 0 <= f <= STK ->
  regions_wf (fsT_regions_args f rs) = true ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (Ereg regs (fs_extraT ++ xs)) (fsT_regions_args f rs) ->
  atoms_ok (Ereg regs (fs_extraT ++ xs)) gf ->
  st_ok tfibsegs (Ereg regs (fs_extraT ++ xs)) (fss0T_args pc f rs gf)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros B STK f ly S U W regs mem md ch pc rs gf xs Hgot Hcell HPRE Hf Hwf Hrs Hdj Hgf.
pose proof (fsw_T_regions_okX B STK f ly S U W regs mem md ch xs Hgot Hcell HPRE Hf) as H3.
pose proof (fsw_sp B STK ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
rewrite restrict_mkst_fx. unfold fss0T_args.
assert (E2 : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs (fs_extraT ++ xs) 2 2%bv eq_refl); reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs (fs_extraT ++ xs)) 32) = SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; apply wz; unfold SHADOW_OFF; lia).
apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- unfold fsT_regions_args. apply Forall_forall. intros x Hx. apply in_app_or in Hx as [Hx|Hx];
  [exact (proj1 (Forall_forall _ _) H3 x Hx) | exact (proj1 (Forall_forall _ _) Hrs x Hx)].
- exact Hdj.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|split; [|exact Hgf]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2. change (2 ^ 4) with 16.
    split; [lia | split; [exact Hal16 | lia]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U32, Z.pow_0_r.
    split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
Lemma fsw_entryT_args : forall B STK f ly S U (W : world tfibsegs) regs mem md ch pc rs gf,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> 0 <= f <= STK ->
  regions_wf (fsT_regions_args f rs) = true ->
  Forall (region_ok tfibsegs (Ereg regs fs_extraT) (mrestrict (w_H W) mem)) rs ->
  pairwise_disjoint (Ereg regs fs_extraT) (fsT_regions_args f rs) ->
  atoms_ok (Ereg regs fs_extraT) gf ->
  st_ok tfibsegs (Ereg regs fs_extraT) (fss0T_args pc f rs gf)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros B STK f ly S U W regs mem md ch pc rs gf Hgot Hcell HPRE Hf Hwf Hrs Hdj Hgf.
exact (fsw_entryT_argsX B STK f ly S U W regs mem md ch pc rs gf [] Hgot Hcell HPRE Hf Hwf Hrs Hdj Hgf).
Qed.
(* the use-after-return flag an instrumented function with a fake frame reads before its __asan_stack_malloc test:
   the GOT word (MEASURED: fs.asan-ubsan 0x9fc68, B/YD2l.v as_got_uar of TfibBU; B/YCeg.v:22 A_GOT_uar)
   holds the u32 cell (MEASURED: 0xa8440 = .symtab __asan_option_detect_stack_use_after_return, B/YD2l.v:23 as_uar_cell; B/YCeg.v:23 A_uar_glob), which holds 1
   (AR_const_law, Reusable/YG0d.v:464-466). Pass them to fsw_entryT_args as rs. *)
Definition fs_D_GOT_uar : Z := 0x9fc68.
Definition fs_D_uar_cell : Z := 0xa8440.
Definition fs_got_uar_region : YP09.region :=
  YP09.mkRegion None fs_D_GOT_uar (fs_D_GOT_uar + 8) 0 0 [YP09.mkChunk fs_D_GOT_uar (CVal 8 (SLit fs_D_uar_cell))].
Definition fs_uar_cell_region : YP09.region :=
  YP09.mkRegion None fs_D_uar_cell (fs_D_uar_cell + 4) 0 0 [YP09.mkChunk fs_D_uar_cell (CVal 4 (SLit 1))].
Definition fs_uar_regions : list YP09.region := [fs_got_uar_region; fs_uar_cell_region].
Lemma fsw_val_mem_of_rd32 : forall (H : word -> bool) mem a v,
  rd32 (aview tfibsegs H mem) a v -> val_mem tfibsegs (mrestrict H mem) a 4 v.
Proof.
intros H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte tfibsegs H mem _ _ Hb) as (b & Hm & Hbv & Hrange).
rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma fsw_uar_regions_ok : forall B STK ly S U (W : world tfibsegs) regs mem md ch E,
  as_got_uar B = fs_D_GOT_uar -> as_uar_cell B = fs_D_uar_cell ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch ->
  Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) fs_uar_regions.
Proof.
intros B STK ly S U W regs mem md ch E Hgot Hcell HPRE.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPRE) as HARU.
pose proof HPRE as (HAP & _ & _).
pose proof HAP as (HAR & _).
pose proof asan_consts as (C1 & _ & C3 & _).
destruct (al_const tfibsegs B LAWS ly S W (unpoison U mem) md HAR) as (_ & Kuar & _ & Kgotu).
rewrite Hgot, Hcell in Kgotu. rewrite Hcell in Kuar.
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 x) HARU
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM8 : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U mem)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) mem) a 8 v).
{ intros a v Ha Hb Hv k Hk. rewrite (MB (a + Z.of_nat k) ltac:(lia)). exact (Hv k Hk). }
assert (VM4 : forall a v, 0 <= a -> a + 4 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W) (unpoison U mem)) a 4 v -> val_mem tfibsegs (mrestrict (w_H W) mem) a 4 v).
{ intros a v Ha Hb Hv k Hk. rewrite (MB (a + Z.of_nat k) ltac:(lia)). exact (Hv k Hk). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem) fs_D_GOT_uar 8 fs_D_uar_cell).
{ apply VM8; [unfold fs_D_GOT_uar; lia | unfold fs_D_GOT_uar, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U mem) _ _ Kgotu)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem) fs_D_uar_cell 4 1).
{ apply VM4; [unfold fs_D_uar_cell; lia | unfold fs_D_uar_cell, SHADOW_OFF; lia
  | exact (fsw_val_mem_of_rd32 (w_H W) (unpoison U mem) _ _ Kuar)]. }
unfold fs_uar_regions. constructor; [|constructor; [|constructor]].
- unfold fs_got_uar_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [unfold fs_D_GOT_uar; lia|]. split; [unfold fs_D_GOT_uar; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ 0 fs_D_GOT_uar 8 (SLit fs_D_uar_cell) fs_D_uar_cell);
    [reflexivity | unfold fs_D_uar_cell; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
- unfold fs_uar_cell_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [unfold fs_D_uar_cell; lia|]. split; [unfold fs_D_uar_cell; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ 0 fs_D_uar_cell 4 (SLit 1) 1);
    [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
Qed.
(* ---- a journal whose window top ot lies above the entry sp (FSH_Fn_FORM.md 3a: a caller's real-stack object above the
   callee's sp): the window [spZ regs - STK, ot), size STK + (ot - spZ regs), ot 16-aligned and at most ly_top ly ---- *)
Lemma fsw_apresent_poison : forall B ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= a < 2 ^ 64 ->
  apresent (w_H W) mem a -> apresent (w_H W) (unpoison U mem) a.
Proof.
intros B ly S U W mem md a H Ha (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite (fsw_unpoison_high B ly S U W mem md a H Ha). exact Hb.
Qed.
Lemma fsw_ajournal_init_ot : forall B STK FP ly S U (W : world tfibsegs) regs mem md ch ot,
  afn_preU tfibsegs B STK ly S U W regs mem md ch ->
  spZ regs <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  ajournal tfibsegs B (STK + (ot - spZ regs)) ot FP ly S W (unpoison U mem) md [] ly S W (unpoison U mem) md 0.
Proof.
intros B STK FP ly S U W regs mem md ch ot HPRE Hot Hal Htop Hpot.
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPRE) as HARU.
pose proof HPRE as (HAP & _ & _).
pose proof HAP as (_ & _ & _ & _ & _ & Hstk & Hpres & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop2).
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof (ajournal_init tfibsegs B STK FP ly S W regs (unpoison U mem) md ch HAP) as HJ.
destruct HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres0 & Hstk1 & F5 & HQT).
unfold ajournal.
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|]. split; [exact Hio|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|].
split; [intros a _ _; reflexivity|].
split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact Hgone|].
split.
{ intros a Ha. destruct (Z_lt_le_dec a (spZ regs)) as [L|L]; [apply Hpres; lia|].
  apply (fsw_apresent_poison B ly S U W mem md a HARU); [lia|]. apply Hpot. lia. }
split.
{ unfold astk_ok. split; [exact Hal|]. split; [lia|]. split; [exact Hceil|]. split; [lia|]. split; [lia|].
  split; [exact H47|]. split; [lia|]. split; [exact Htop | exact Htop2]. }
split; [exact F5 | exact HQT].
Qed.
Lemma fsw_ajournal_init_ot_pre : forall B STK FP ly S (W : world tfibsegs) regs mem md ch ot,
  afn_pre tfibsegs B STK ly S W regs mem md ch ->
  spZ regs <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  ajournal tfibsegs B (STK + (ot - spZ regs)) ot FP ly S W mem md [] ly S W mem md 0.
Proof.
intros B STK FP ly S W regs mem md ch ot HPRE.
exact (fsw_ajournal_init_ot B STK FP ly S [] W regs mem md ch ot (fsw_preU_nil _ _ _ _ _ _ _ _ _ HPRE)).
Qed.


(* ---- memory unchanged below a bound (the run's stack writes are all above alloc_ceiling) ---- *)
Definition same_below (m m' : word -> option byte) (lo : Z) : Prop :=
  forall x, 0 <= x < lo -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Lemma same_below_refl : forall m lo, same_below m m lo.
Proof. intros m lo x _. reflexivity. Qed.
Lemma same_below_trans : forall m1 m2 m3 lo, same_below m1 m2 lo -> same_below m2 m3 lo -> same_below m1 m3 lo.
Proof. intros m1 m2 m3 lo H1 H2 x Hx. rewrite (H2 x Hx). exact (H1 x Hx). Qed.
Lemma same_below_mono : forall m m' lo lo', same_below m m' lo -> lo' <= lo -> same_below m m' lo'.
Proof. intros m m' lo lo' H Hl x Hx. apply H. lia. Qed.
(* a run whose one region is a stack window at or above lo leaves memory below lo unchanged *)
Lemma same_below_frame1 : forall E (r : YP09.region) m m' lo,
  frame_of E [r] m m' -> lo <= base_val E (YP09.r_base r) + YP09.r_wlo r -> lo <= 2 ^ 64 -> same_below m m' lo.
Proof.
intros E r m m' lo HF Hlo H64 x Hx.
apply (frame_of_one E m m' r lo (base_val E (YP09.r_base r) + YP09.r_whi r) (Z_to_bv 64 x) HF Hlo ltac:(lia)).
left. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma mbyte_below : forall (H : word -> bool) m m' lo a, same_below m m' lo -> 0 <= a < lo ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H m m' lo a Hs Ha. unfold mbyte, mrestrict. rewrite (Hs a Ha). reflexivity. Qed.
Lemma aview_below : forall (H : word -> bool) m m' lo a, same_below m m' lo -> 0 <= a < lo ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' lo a Hs Ha. unfold aview. rewrite (mbyte_below H m m' lo a Hs Ha). reflexivity. Qed.
Lemma val_mem_below : forall (H : word -> bool) m m' lo a (n : nat) v, same_below m m' lo ->
  0 <= a -> a + Z.of_nat n <= lo -> val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' lo a n v Hs H0 Hn Hv k Hk. rewrite (mbyte_below H m m' lo (a + Z.of_nat k) Hs ltac:(lia)). exact (Hv k Hk).
Qed.
Lemma fs_glob_below : forall (W : world tfibsegs) m m' live peak cnt fail,
  same_below m m' alloc_ceiling -> fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hs (G1 & G2 & G3 & G4 & R).
pose proof asan_consts as (C1 & _).
assert (VB : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v).
{ intros a v Ha Hb Hv. exact (val_mem_below (w_H W) m m' alloc_ceiling a 8 v Hs Ha Hb Hv). }
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.
Lemma arodata_below : forall (B : asyms) (W : world tfibsegs) m m',
  same_below m m' alloc_ceiling -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros B W m m' Hs HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
rewrite (aview_below (w_H W) m m' alloc_ceiling a Hs Hb). exact (HR a Ha Ho He).
Qed.
(* cstr_ok's clauses are found by their form, not their position: the memory-free ones carry over unchanged, the four
   memory ones (the bytes, range_addressable, shadow_hull_vis, the visible rest of the NUL's word) through aview below
   alloc_ceiling *)
Lemma cstr_ok_below : forall (W : world tfibsegs) m m' p l,
  same_below m m' alloc_ceiling -> cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W m' p l.
Proof.
intros W m m' p l Hs H.
pose proof asan_consts as (C1 & _).
assert (AV : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a)
  by (intros a Ha; exact (aview_below (w_H W) m m' alloc_ceiling a Hs Ha)).
unfold cstr_ok, cstr in H |- *.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
repeat match goal with |- _ /\ _ => split end; try assumption; lazymatch goal with
  | Hg : garr8 _ (mrestrict _ m) p (l ++ [0]) |- garr8 _ _ p (l ++ [0]) =>
      apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg); intros a Ha; rewrite length_app in Ha; cbn [length] in Ha;
      apply (mbyte_below _ m m' alloc_ceiling a Hs); lia
  | Hra : range_addressable (aview _ _ m) ?o ?q ?n |- range_addressable (aview _ _ m') ?o ?q ?n =>
      intros x Hx; destruct (Hra x Hx) as (s & Hs1 & Hs2); exists s; split; [|exact Hs2];
      rewrite AV; [exact Hs1|]; unfold shadow_of_addr, SHADOW_OFF; lia
  | Hhv : shadow_hull_vis (aview _ _ m) ?q ?n |- shadow_hull_vis (aview _ _ m') ?q ?n =>
      intros s Hsr; rewrite AV; [exact (Hhv s Hsr)|]; unfold shadow_addr, SHADOW_OFF in Hsr; lia
  | Htl : forall a, _ -> aview _ _ m a <> None |- forall a, _ -> aview _ _ m' a <> None =>
      (* the word holding the NUL ends at or below alloc_ceiling: p + |l| + 1 <= alloc_ceiling and alloc_ceiling is
         4096-aligned (YM05.alloc_ceiling_value), so (p + |l|) / 8 * 8 + 8 <= alloc_ceiling *)
      intros a Ha; rewrite AV; [exact (Htl a Ha)|];
      pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia));
      pose proof (proj2 YM05.alloc_ceiling_value); lia
  end.
Qed.

(* ---- reading the symbolic state ---- *)
Lemma fsw_region_nth : forall E ss ms i r,
  st_ok tfibsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok tfibsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok tfibsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma fsw_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem tfibsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok tfibsegs E m b od w e v Hck He Hv Hw).
Qed.
(* a register the run left as its entry atom still holds the entry value *)
Lemma fsw_reg_atom : forall (H : word -> bool) regs0 extra ss ms (r r' : bv 5) n,
  st_ok tfibsegs (Ereg regs0 extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 ->
  Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs0 r'.
Proof.
intros H regs0 extra ss ms r r' n HS Hr Hn.
rewrite (st_ok_restrict_reg tfibsegs H _ ss ms r HS), Hr, fsw_SOff0. exact (ew_Ereg_nat regs0 extra n r' Hn).
Qed.
Lemma fsw_reg_off : forall (H : word -> bool) E ss ms (r : bv 5) n z v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  bv_unsigned (ew E n) = v -> 0 <= v + z < 2 ^ 64 -> bv_unsigned (getr (ms_regs ms) r) = v + z.
Proof.
intros H E ss ms r n z v HS Hr Hv Hz.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr, denot_SOff, Hv. apply zcanon_id. unfold M64. lia.
Qed.
Lemma fsw_reg_lit : forall (H : word -> bool) E ss ms (r : bv 5) z,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SLit z -> 0 <= z < 2 ^ 64 ->
  getr (ms_regs ms) r = Z_to_bv 64 z.
Proof.
intros H E ss ms r z HS Hr Hz. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr.
apply bv_eq. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)). rewrite U_lit by exact Hz.
rewrite unsigned_lit_small by exact Hz. reflexivity.
Qed.
(* a callee-saved register the caller left as its entry atom up to a call, read after the call *)
Lemma fsw_kept_reg : forall (H : word -> bool) regs0 extra0 ssC msC regs2 extra2 (r : bv 5) n,
  st_ok tfibsegs (Ereg regs0 extra0) ssC (restrict H msC) ->
  sr_get (ss_regs ssC) r = SOff n 0 -> Z.of_nat n = bv_unsigned r ->
  aregs_preserved (ms_regs msC) regs2 -> acallee_saved (bv_unsigned r) ->
  sv_denot (Ereg regs2 extra2) (SOff n 0) = getr regs0 r.
Proof.
intros H regs0 extra0 ssC msC regs2 extra2 r n HS Hr Hn HP Hcs.
rewrite fsw_SOff0, (ew_Ereg_nat regs2 extra2 n r Hn).
pose proof (HP (bv_unsigned r) Hcs) as E. rewrite Z_to_bv_bv_unsigned in E. rewrite E.
exact (fsw_reg_atom H regs0 extra0 ssC msC r r n HS Hr Hn).
Qed.
Lemma fsw_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hc. pose proof (HP _ Hc) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Lemma fsw_reg_extra : forall (H : word -> bool) regs extra ss ms (r : bv 5) j,
  st_ok tfibsegs (Ereg regs extra) ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff (32 + j) 0 ->
  getr (ms_regs ms) r = nth j extra (Z_to_bv 64 0).
Proof.
intros H regs extra ss ms r j HS Hr. rewrite (st_ok_restrict_reg tfibsegs H _ ss ms r HS), Hr, fsw_SOff0.
apply ew_Ereg_extra.
Qed.
(* the value of an expected callee-saved register that is the frame's sp back up, or a reloaded extra atom *)
Lemma fsw_sp_back : forall regs extra regs0 f, bv_unsigned (ew (Ereg regs extra) 2) = spZ regs0 - f ->
  sv_denot (Ereg regs extra) (SOff 2 f) = getr regs0 2.
Proof.
intros regs extra regs0 f H. apply bv_eq. rewrite denot_SOff, H. unfold spZ.
replace (bv_unsigned (getr regs0 2) - f + f) with (bv_unsigned (getr regs0 2)) by lia.
apply zcanon_id. unfold M64. apply u64_range.
Qed.
Lemma fsw_extra_atom : forall regs extra j, sv_denot (Ereg regs extra) (SOff (32 + j) 0) = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j. rewrite fsw_SOff0. apply ew_Ereg_extra. Qed.
(* the callee-saved registers at the end, from what the symbolic state says of each *)
Lemma fsw_preserved : forall (H : word -> bool) E ss ms regs0 (expect : bv 5 -> sv),
  st_ok tfibsegs E ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (expect r)) CALLEE_SAVED = true ->
  (forall r, In r CALLEE_SAVED -> sv_denot E (expect r) = getr regs0 r) ->
  aregs_preserved regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 expect HS Hcs Hex r Hr.
assert (Hin : In (Z_to_bv 5 r : bv 5) CALLEE_SAVED).
{ unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [->|Hc]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
  subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg tfibsegs H E ss ms _ HS), Hq. exact (Hex _ Hin).
Qed.

(* ---- after a program call: the composed journal and the symbolic state at the return address ---- *)
Definition fstk_ret (f : Z) (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) 0 f 0 f cs.
Definition fss_ret (pc f : Z) (cs : list YP09.chunk) : sstate :=
  mkSS pc sr_atoms [fstk_ret f cs] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Lemma chunk_ok_mbyte : forall E (m m' : word -> option byte) base (c : YP09.chunk),
  (forall i, 0 <= i < YP09.c_len c -> mbyte tfibsegs m' (base + YP09.c_off c + i) = mbyte tfibsegs m (base + YP09.c_off c + i)) ->
  YP09.chunk_ok tfibsegs E m base c -> YP09.chunk_ok tfibsegs E m' base c.
Proof. intros E m m' base c Hm Hc i Hi. destruct (Hc i Hi) as (b & H1 & H2). exists b. rewrite Hm by exact Hi. auto. Qed.
Lemma fsw_after_call : forall B STK sp0 ly S W mem md lyc Sc memC mdC k STKc f regsC ly' S' W' regs' mem' md' kc
  extra cs r,
  ajournal tfibsegs B STK sp0 [] ly S W mem md [] lyc Sc W memC mdC k ->
  ajournal tfibsegs B STKc (spZ regsC) [] lyc Sc W memC mdC [] ly' S' W' mem' md' kc ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) memC) (sp0 - f)) cs ->
  ajournal tfibsegs B STK sp0 [] ly S W mem md [] ly' S' W' mem' md' (k + kc) /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret r f cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 ly S W mem md lyc Sc memC mdC k STKc f regsC ly' S' W' regs' mem' md' kc extra cs r
  HJ HJc HP Hsp Hf HSc Hbud Hal Hwf Hin Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 [] ly S W mem md [] ly' S' W' mem' md' (k + kc)).
{ pose proof (ajournal_sub tfibsegs B LAWS fs_segs_low STK sp0 [] ly S W mem md [] lyc Sc W memC mdC k
    STKc (spZ regsC) [] [] ly' S' W' mem' md' kc HJ HJc ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as H. exact H. }
split; [exact HJ2|].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Esp : getr regs' 2 = getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' extra) 2) = sp0 - f) by (rewrite (ew_Ereg_nat regs' extra 2 2%bv eq_refl); exact Usp).
rewrite restrict_mkst_fx. unfold fss_ret. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs). apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
    destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs). apply F1; [lia | intros Hx; lia].
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
Qed.
(* fsw_after_call in U form: the caller's journal runs over unpoison U mem .. unpoison Uc memC, the callee's (fpostU's)
   over unpoison Uc memC .. unpoison U' mem'; the frame's chunks are read on the machine's memory memC at the call and the
   resumed state on the machine's memory mem' (the caller's frame is stack: no user-poisoned shadow byte at either end) *)
Lemma fsw_after_callU : forall B STK sp0 ly S U W mem md lyc Sc Uc memC mdC k STKc f regsC ly' S' U' W' regs' mem' md'
  kc extra cs r,
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B STKc (spZ regsC) [] lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  regions_wf [fstk_ret f cs] = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) memC) (sp0 - f)) cs ->
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' (k + kc) /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret r f cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 ly S U W mem md lyc Sc Uc memC mdC k STKc f regsC ly' S' U' W' regs' mem' md' kc extra cs r
  HJ HARUc HJc OK' PO' HP Hsp Hf HSc Hbud Hal Hwf Hin Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' (k + kc)).
{ pose proof (ajournal_sub tfibsegs B LAWS fs_segs_low STK sp0 [] ly S W (unpoison U mem) md [] lyc Sc W
    (unpoison Uc memC) mdC k STKc (spZ regsC) [] [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as H. exact H. }
split; [exact HJ2|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR2 | split; [exact OK' | exact PO']]).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (Esp : getr regs' 2 = getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sp0 - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' extra) 2) = sp0 - f) by (rewrite (ew_Ereg_nat regs' extra 2 2%bv eq_refl); exact Usp).
rewrite restrict_mkst_fx. unfold fss_ret. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
    destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs).
    rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' _ HARU') by lia.
    rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC _ HARUc) by lia.
    apply F1; [lia | intros Hx; lia].
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. assert (f mod 16 = 0) as -> by exact Hal. reflexivity.
Qed.

(* ---- the fake-frame prologue's re-align (`addi sp, sp, -F; addi s0, sp, F; andi sp, sp, -32`): the engine keeps the
   AND symbolic, so the walk re-seats sp on a FRESH ATOM. The donor's steps (cgif A/AChf.v:140-163, pb_flushFrame):
   read the realigned value (cgif A/ACer.v:156 denot_and_m32, ported below), make it a fresh atom, set sp to it and add
   its 32-alignment fact. fsw_reseat_atom is the generic state step (a Theorem Labs lane's crcs_reseat_atom, over the core's
   YP03.st_ok_agree / env_agree_ewset / st_ok_add_fact, YI08.st_ok_set_reg, YI0n.st_ok_add_region'), fsw_realign32U
   the two together at the realigned register. ---- *)
Lemma land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = 32 * (x / 32).
Proof.
intros x Hx.
assert (E1 : 2 ^ 64 - 32 = Z.ldiff (Z.ones 64) (Z.ones 5)) by reflexivity. rewrite E1.
rewrite Z.ldiff_land, Z.land_assoc, <- Z.ldiff_land.
rewrite Z.land_ones, Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. lia.
Qed.
Lemma denot_and_m32 : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v + c -> v + c < 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit (-32))) = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E n v c Hn H0 H1 Hv. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom_off E n v c Hn) by lia.
change (zcanon (-32)) with (2 ^ 64 - 32). rewrite land_m32 by lia. apply zcanon_id. unfold M64.
split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
pose proof (Z.mul_div_le (v + c) 32 ltac:(lia)). lia.
Qed.
(* what the realigned sp is worth: 32 * (x / 32) for x = the sp after the frame drop, between x - 16 and x *)
Lemma fsw_realign_facts : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= 32 * (x / 32) <= x /\ (32 * (x / 32)) mod 32 = 0 /\ (32 * (x / 32)) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* re-seat a register on a fresh atom: the atom takes the register's machine value, the register becomes SOff n 0, and
   the state gains the region [lo, hi) at that atom and a fact for it *)
Lemma fsw_reseat_atom : forall E ss ms (r : bv 5) n lo hi af,
  st_ok tfibsegs E ss ms -> ss_atoms_lt n ss = true -> r <> 0%bv ->
  YP09.region_wf (YP09.mkRegion (Some n) lo hi lo hi []) = true ->
  region_ok tfibsegs (ewset E n (YK11.getr (ms_regs ms) r)) (ms_mem ms) (YP09.mkRegion (Some n) lo hi lo hi []) ->
  all_disjoint (ewset E n (YK11.getr (ms_regs ms) r)) (YP09.mkRegion (Some n) lo hi lo hi []) (ss_mem ss) ->
  afact_ok (ewset E n (YK11.getr (ms_regs ms) r)) n af ->
  st_ok tfibsegs (ewset E n (YK11.getr (ms_regs ms) r))
    (add_atom (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0))
       (YP09.mkRegion (Some n) lo hi lo hi [] :: ss_mem ss) (ss_resv ss) (ss_facts ss)) n af) ms.
Proof.
intros E ss ms r n lo hi af HS Hat Hr Hwf Hok Hdj Haf.
set (E' := ewset E n (YK11.getr (ms_regs ms) r)) in *.
pose proof (st_ok_agree tfibsegs n E E' ss ms HS (env_agree_ewset E n _) Hat) as HS1.
assert (Hv : YK11.getr (ms_regs ms) r = sv_denot E' (SOff n 0))
  by (unfold E'; rewrite fsw_SOff0, ew_ewset_same; reflexivity).
pose proof (st_ok_set_reg tfibsegs E' ss ms r (SOff n 0) HS1 Hr Hv) as HS2.
pose proof (st_ok_add_region' tfibsegs E' _ ms _ HS2 Hwf Hok Hdj) as HS3.
exact (st_ok_add_fact tfibsegs E' _ ms n af HS3 Haf).
Qed.
(* the machine value of a register the run left as `rY AND -32` *)
Lemma fsw_realign_val : forall E ss ms (r : bv 5) n c v,
  st_ok tfibsegs E ss ms -> sr_get (ss_regs ss) r = SAlu ALU_AND (SOff n c) (SLit (-32)) ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  YK11.getr (ms_regs ms) r = Z_to_bv 64 (32 * ((v + c) / 32)).
Proof.
intros E ss ms r n c v HS Hsr Hn Hv Hc.
rewrite (st_ok_reg tfibsegs E ss ms r HS), Hsr.
exact (denot_and_m32 E n v c Hn ltac:(lia) ltac:(lia) Hv).
Qed.
(* the re-align as one step: the register's new value is a fresh atom worth 32 * ((v + c) / 32) *)
Lemma fsw_realign32U : forall E ss ms (r : bv 5) n c v nn lo hi,
  st_ok tfibsegs E ss ms -> sr_get (ss_regs ss) r = SAlu ALU_AND (SOff n c) (SLit (-32)) ->
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  ss_atoms_lt nn ss = true -> r <> 0%bv ->
  YP09.region_wf (YP09.mkRegion (Some nn) lo hi lo hi []) = true ->
  region_ok tfibsegs (ewset E nn (Z_to_bv 64 (32 * ((v + c) / 32)))) (ms_mem ms)
    (YP09.mkRegion (Some nn) lo hi lo hi []) ->
  all_disjoint (ewset E nn (Z_to_bv 64 (32 * ((v + c) / 32)))) (YP09.mkRegion (Some nn) lo hi lo hi []) (ss_mem ss) ->
  afact_ok (ewset E nn (Z_to_bv 64 (32 * ((v + c) / 32)))) nn (mkAF lo hi 5) ->
  st_ok tfibsegs (ewset E nn (Z_to_bv 64 (32 * ((v + c) / 32))))
    (add_atom (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff nn 0))
       (YP09.mkRegion (Some nn) lo hi lo hi [] :: ss_mem ss) (ss_resv ss) (ss_facts ss)) nn (mkAF lo hi 5)) ms.
Proof.
intros E ss ms r n c v nn lo hi HS Hsr Hn Hv Hc Hat Hr Hwf Hok Hdj Haf.
pose proof (fsw_realign_val E ss ms r n c v HS Hsr Hn Hv Hc) as Hval.
rewrite <- Hval in Hok, Hdj, Haf |- *.
exact (fsw_reseat_atom E ss ms r nn lo hi (mkAF lo hi 5) HS Hat Hr Hwf Hok Hdj Haf).
Qed.

(* ---- the state after a program call of a function whose sp was re-aligned: its saved registers sit at literal
   offsets from s0 (the entry sp, kept across the call), not from the resumed sp, so the frame region is based at the
   s0 atom (8) and the window is [sp0 + lo, sp0 + hi) with lo <= hi <= 0 ---- *)
Definition fs_ret_s0_region (lo hi : Z) (cs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 8%nat) lo hi lo hi cs.
Definition fss_ret_s0 (pc lo hi : Z) (cs : list YP09.chunk) : sstate :=
  mkSS pc sr_atoms [fs_ret_s0_region lo hi cs] None (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Lemma fsw_after_callU_s0 : forall B STK sp0 ly S U W mem md lyc Sc Uc memC mdC k STKc sp1 regsC ly' S' U' W' regs'
  mem' md' kc extra cs r lo hi,
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B STKc sp1 [] lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' -> spZ regsC = sp1 ->
  YK11.getr regs' 8%bv = Z_to_bv 64 sp0 ->
  sp0 - STK <= sp1 - STKc -> sp1 <= sp0 -> sp0 - STK <= sp0 + lo -> sp1 <= sp0 + lo -> lo <= hi -> hi <= 0 ->
  regions_wf [fs_ret_s0_region lo hi cs] = true ->
  Forall (fun c => lo <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= hi) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) memC) sp0) cs ->
  ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' (k + kc) /\
  st_ok tfibsegs (Ereg regs' extra) (fss_ret_s0 r lo hi cs)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK sp0 ly S U W mem md lyc Sc Uc memC mdC k STKc sp1 regsC ly' S' U' W' regs' mem' md' kc extra cs r lo hi
  HJ HARUc HJc OK' PO' HP Hsp Hs0 Hlo1 Hhi1 Hwin Habove Hlohi Hhi0 Hwf Hin Hcs.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HJ2 : ajournal tfibsegs B STK sp0 [] ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' (k + kc)).
{ pose proof (ajournal_sub tfibsegs B LAWS fs_segs_low STK sp0 [] ly S W (unpoison U mem) md [] lyc Sc W
    (unpoison Uc memC) mdC k STKc sp1 [] [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as H. exact H. }
split; [exact HJ2|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR2 | split; [exact OK' | exact PO']]).
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
assert (E8 : bv_unsigned (ew (Ereg regs' extra) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs' extra 8 8%bv eq_refl), Hs0; apply wz; lia).
rewrite restrict_mkst_fx. unfold fss_ret_s0. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor]. unfold region_ok, fs_ret_s0_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E8. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  + apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) Hin c Hc) as Hci.
    pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
    apply (chunk_ok_mbyte _ (mrestrict (w_H W) memC)); [|exact Hck].
    destruct Hci as [Hc0 Hc1]. intros i Hi. apply (mbyte_of_aview tfibsegs).
    rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' _ HARU') by lia.
    rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC _ HARUc) by lia.
    apply F1; [lia | intros Hx; lia].
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E8.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal16 | lia]].
Qed.

(* ---- U form: the steps of a RUNTIME call. The caller holds the journal over the unpoisoned memory and ARU over the
   machine's; the callee's contract (FSupoisonU's ARU forms, FSH_Gen's rt_post_roU) takes ecall_preU / ecall_preU_k and
   gives back ARU and a frame. These three put the journal and ARU back together; they are generic in FP (the write
   premise is the core's awr_byte at the caller's FP and entry frames, or awr_byte0 for a dest window) and in the
   callee's own post Q. ---- *)
Lemma fsw_ecall_preU_at : forall B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k regsT (o : Z),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison Uc memT) mdc k ->
  ARU tfibsegs B lyc Sc Uc W memT mdc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  ecall_preU tfibsegs B lyc Sc Uc W regsT memT mdc.
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k regsT o HJ HARU Hsp Hal Hneg Hbud Hra Hgp Htp.
pose proof HARU as (_ & OK & PO).
split; [|split; [exact OK | exact PO]].
eapply (ecall_pre_at tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison Uc memT) mdc k regsT o);
  eassumption.
Qed.
Lemma fsw_ecall_preU_k_at : forall B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k regsT (o K : Z),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison Uc memT) mdc k ->
  ARU tfibsegs B lyc Sc Uc W memT mdc ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK -> 0 <= K -> K - o <= STK ->
  YK0s.ret_ok (YK11.getr regsT 1) -> YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  ecall_preU_k tfibsegs B K lyc Sc Uc W regsT memT mdc.
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k regsT o K HJ HARU Hsp Hal Hneg Hbud HK0 HKb
  Hra Hgp Htp.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
split.
{ exact (fsw_ecall_preU_at B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k regsT o HJ HARU Hsp Hal Hneg Hbud
    Hra Hgp Htp). }
split; [rewrite Eslo, Hsp; lia|].
intros a Ha. rewrite Hsp in Ha.
apply (fsw_apresent_unpoison B lyc Sc Uc W memT mdc a HARU); [lia|]. apply Hpres. lia.
Qed.
(* the write window a runtime call may touch, as dest_ok asks it, from the caller's awr_byte0 (YCbq.v
   awr_byte_present: awr_byte's image and entry-frame arms give no presence) *)
Lemma fsw_dest_okU : forall B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k regsT d n,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison Uc memT) mdc k ->
  ARU tfibsegs B lyc Sc Uc W memT mdc ->
  (forall a, d <= a < d + n -> awr_byte0 STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
     ~ (spZ regsT - ESTACK <= a < spZ regsT)) ->
  dest_ok tfibsegs B lyc Sc W regsT (unpoison Uc memT) d n.
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k regsT d n HJ HARU Hd a Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (Hd a Ha) as [Hw Hns].
assert (HP : apresent (w_H W) (unpoison Uc memT) a /\ ~ aowned B lyc Sc a)
  by (eapply awr_byte_present; eassumption).
split; [apply (apresent_writable tfibsegs); exact (proj1 HP)|].
split; [exact (proj2 HP) | exact Hns].
Qed.
(* the callee returned (its post is the ARU form's: the world kept, ARU at U', a frame outside Wr, presence kept):
   put the caller's journal back on the new memory and keep the callee's own facts Q *)
Lemma fsw_intrin_atU : forall B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k U' (Wr : Z -> Prop) raw c0
  (Q : bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison Uc memT) mdc k ->
  SRr tfibsegs W c0
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = mkCfg (mkst regs' raw mem' (seg_rom tfibsegs)) md' /\
       ARU tfibsegs B lyc Sc U' W mem' md' /\ same_but_materialized mdc md' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
          aview tfibsegs (w_H W) (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison Uc memT) a) /\
       (forall a, apresent (w_H W) (unpoison Uc memT) a -> apresent (w_H W) (unpoison U' mem') a) /\
       Q regs' mem' md') ->
  (forall a, Wr a -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  SRr tfibsegs W c0
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
       ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U' mem2) md2 k /\
       ARU tfibsegs B lyc Sc U' W mem2 md2 /\ Q regs2 mem2 md2).
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memT mdc k U' Wr raw c0 Q HJ HC HW.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply SRr_mono; first [ solve [exact HC] | lazymatch goal with |- forall _, _ => idtac end ].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HARU2 & Hsame & Hfr & Hgr & HQ).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [|split; [exact HARU2 | exact HQ]].
eapply (ajournal_after_write tfibsegs B LAWS fs_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W
  (unpoison Uc memT) mdc k (unpoison U' mem2) md2 Wr Sc own HJ Hfr Hgr Hsame).
all: first [ solve [intros a Ha; left; exact (HW a Ha)] | solve [exact (proj1 HARU2)] | solve [reflexivity]
           | solve [lia] | solve [exact Hfrs] | solve [exact HQT] ].
Qed.
(* the same step without a call: the walk's own stores, as one journal step over the unpoisoned memories *)
Lemma fsw_ajournal_writeU : forall B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memc mdc k U' memc' mdc'
  (Wr : Z -> Prop),
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison Uc memc) mdc k ->
  ARU tfibsegs B lyc Sc U' W memc' mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a ->
     aview tfibsegs (w_H W) (unpoison U' memc') a = aview tfibsegs (w_H W) (unpoison Uc memc) a) ->
  (forall a, apresent (w_H W) (unpoison Uc memc) a -> apresent (w_H W) (unpoison U' memc') a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte tfibsegs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U' memc') mdc' k.
Proof.
intros B STK sp0 FP ly S W0 mem md own lyc Sc Uc W memc mdc k U' memc' mdc' Wr HJ HARU' Hfr Hgr Hsame HW.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
eapply (ajournal_after_write tfibsegs B LAWS fs_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W
  (unpoison Uc memc) mdc k (unpoison U' memc') mdc' Wr Sc own HJ Hfr Hgr Hsame).
all: first [ solve [intros a Ha; left; exact (HW a Ha)] | solve [exact (proj1 HARU')] | solve [reflexivity]
           | solve [lia] | solve [exact Hfrs] | solve [exact HQT] ].
Qed.
(* a callee that returns its own journal (the allocator leaves, the realloc leaf): compose it into the caller's,
   keeping the caller's FP; the callee's FP1 must lie in the caller's FP inside a live block, or in a tmp block
   (the core's ajournal_sub rule) *)
Lemma fsw_rt_atU : forall B STK sp0 FP ly S W mem md own lyc Sc Uc W1 memc mdc k STK1 sp1 FP1 nf ly2 S2 U2 W2 mem2
  md2 k1,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own lyc Sc W1 (unpoison Uc memc) mdc k ->
  ajournal tfibsegs B STK1 sp1 FP1 lyc Sc W1 (unpoison Uc memc) mdc nf ly2 S2 W2 (unpoison U2 mem2) md2 k1 ->
  upoison_ok B ly2 S2 U2 -> upoisoned tfibsegs W2 mem2 U2 ->
  sp0 - STK <= sp1 - STK1 -> sp1 <= sp0 ->
  (forall a, inFP FP1 a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
     in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
  ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 (unpoison U2 mem2) md2 (k + k1) /\
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2.
Proof.
intros B STK sp0 FP ly S W mem md own lyc Sc Uc W1 memc mdc k STK1 sp1 FP1 nf ly2 S2 U2 W2 mem2 md2 k1
  HJ HJc OK2 PO2 Hlo Hhi HF.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W mem md (nf ++ own) ly2 S2 W2 (unpoison U2 mem2) md2 (k + k1)).
{ exact (ajournal_sub tfibsegs B LAWS fs_segs_low STK sp0 FP ly S W mem md own lyc Sc W1 (unpoison Uc memc) mdc k
    STK1 sp1 FP1 nf ly2 S2 W2 (unpoison U2 mem2) md2 k1 HJ HJc Hlo Hhi
    ltac:(intros a Ha; destruct (HF a Ha) as [Hx|Hx];
          [left; exact Hx | right; first [exact Hx | left; exact Hx]])). }
split; [exact HJ2|].
split; [exact (proj1 HJ2)|]. split; [exact OK2 | exact PO2].
Qed.
End e.

(* ---- U form: one engine run (YCbq.v SRr_run_AJ and its run_to / tok forms) with the symbolic state read on the
   machine's memory and the journal kept over that memory with U's shadow bytes read as 0. The run writes only bytes
   awr_byte allows, none of them owned (YCbq.v awr_byte_cases); U's shadow bytes are owned (FSupoison.ush_facts), so the
   run leaves them and ARU holds after it. ---- *)
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Definition run_post_AJU (B : asyms) (W : world tfibsegs) (E : env) (ss ss' : sstate) (ms : machine_state)
  (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs) (mem : word -> option byte)
  (md : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (U : list (Z * Z)) (mdc : Model) (k : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall ms' mat',
  st_ok tfibsegs E ss' (restrict (w_H W) ms') ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms'))
    (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Definition run_post_tok_AJU (B : asyms) (W : world tfibsegs) (E : env) (K : nat) (Bx : sv) (SH : list shent)
  (ss : sstate) (st' : shst) (ms : machine_state)
  (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world tfibsegs) (mem : word -> option byte)
  (md : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (U : list (Z * Z)) (mdc : Model) (k : Z)
  (Q : world tfibsegs -> config -> Prop) : Prop :=
  forall ws ms' mat',
  length ws = sh_j st' ->
  st_ok tfibsegs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
  sh_ok tfibsegs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms'))
    (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr tfibsegs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* the machine's memory after the run, ms_mem (unrestrict ...), as the engine gives it: the journal over its unpoisoned
   reading (YCbq.v ajournal_exec over the unpoisoned memories) and ARU *)
Lemma fsw_exec_U : forall B (W : world tfibsegs) E (ss : sstate) ms msr' STK sp0 FP (ly : alayout) (S : astate)
  (W0 : world tfibsegs) mem md own (lyc : alayout) (Sc : astate) U mdc k model',
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (ms_mem msr') ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (ms_mem msr') ->
  hclean (w_H W) msr' ->
  same_but_materialized mdc model' ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')))
    (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc) k /\
  ARU tfibsegs B lyc Sc U W (ms_mem (unrestrict (w_H W) (ms_mem ms) msr'))
    (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc).
Proof.
intros B W E ss ms msr' STK sp0 FP ly S W0 mem md own lyc Sc U mdc k model' HJ HARU Hwr Hfr Hgr Hcl Hsame.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
assert (Fr : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) ->
  mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) x = mrestrict (w_H W) (ms_mem ms) x)
  by (rewrite Hmm; exact Hfr).
assert (Gr : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem (unrestrict (w_H W) (ms_mem ms) msr'))))
  by (rewrite Hmm; exact Hgr).
assert (Hid : forall x : word, w_H W x = true -> ms_mem (unrestrict (w_H W) (ms_mem ms) msr') x = ms_mem ms x)
  by (intros x Hx; cbn [unrestrict ms_mem]; unfold munrestrict; rewrite Hx; reflexivity).
assert (HJ' : ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W
  (unpoison U (ms_mem (unrestrict (w_H W) (ms_mem ms) msr'))) (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc) k).
{ eapply (ajournal_exec tfibsegs B LAWS fs_segs_low) with (Wr := in_wrange E (ss_mem ss)).
  all: first
    [ solve [exact HJ]
    | solve [exact Hwr]
    | solve [intros x Hx; pose proof (Fr x Hx) as Ex; revert Ex; unfold mrestrict, unpoison;
             destruct (w_H W x); [intros _; reflexivity|];
             destruct (in_ush U (bv_unsigned x)); [intros _; reflexivity | intros Ex; exact Ex]]
    | solve [intros x; pose proof (Gr x) as Gx; intros Hx; revert Gx Hx; unfold mrestrict, unpoison;
             destruct (w_H W x); [intros _ Hx; exact Hx|];
             destruct (in_ush U (bv_unsigned x)); [intros _ _; discriminate | intros Gx Hx; exact (Gx Hx)]]
    | solve [intros x Hx; unfold unpoison; destruct (in_ush U (bv_unsigned x)); [reflexivity | exact (Hid x Hx)]]
    | solve [rewrite <- (same_but_materialized_wvb mdc model' Hsame); exact Hsame] ]. }
split; [exact HJ'|].
pose proof HARU as (_ & OK & PO).
split; [exact (proj1 HJ')|]. split; [exact OK|].
intros s Hs.
assert (UF : aowned B lyc Sc s /\ SHADOW_OFF <= s < kHighMemBeg) by (eapply ush_facts; eassumption).
destruct UF as (Hown & L1 & L2). pose proof asan_consts as (_ & _ & C3 & _).
assert (Hs64 : 0 <= s < 2 ^ 64) by (unfold SHADOW_OFF in L1; lia).
rewrite <- (PO s Hs). apply (aview_eq_of tfibsegs). apply Fr. rewrite (wz s Hs64). intros Hin.
exact (proj1 (awr_byte_cases tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s HJ (Hwr s Hin)) Hown).
Qed.
Lemma fsw_chain_AJU : forall B W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q,
  msteps tfibsegs (restrict (w_H W) ms) msr' ->
  st_ok tfibsegs E ss' msr' ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) ->
  run_post_AJU B W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros B W E ss ss' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q Hms HS' Hfr HARU HJ Hwr Hk.
apply (SRr_msteps tfibsegs fs_wx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows tfibsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
destruct (fsw_exec_U B W E ss ms msr' STK sp0 FP ly S W0 mem md own lyc Sc U mdc k model' HJ HARU Hwr Hfr Hgr Hcl Hsame)
  as [HJ' HARU'].
apply (Hk (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model')).
- rewrite Hrr. exact HS'.
- exact HJ'.
- exact HARU'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma fsw_run_AJU : forall B tbl (tbl_ok : table_ok tfibsegs tbl) W n E ss ss' st ms STK sp0 FP ly S W0 mem md own
  lyc Sc U mdc k Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_runN tfibsegs tbl n ss = (ss', st) ->
  match st with RS_ecall => False | _ => True end ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) ->
  run_post_AJU B W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros B tbl tbl_ok W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q HS Hrun Hst HARU HJ Hwr Hk.
destruct (msteps_run_gen tfibsegs tbl tbl_ok n E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply fsw_chain_AJU.
all: first [ solve [exact Hms] | solve [exact Hfr] | solve [exact HARU] | solve [exact HJ] | solve [exact Hwr]
           | solve [exact Hk] | solve [destruct st; [exact HS' | destruct Hst | exact HS']] ].
Qed.
Lemma fsw_run_to_AJU : forall B tbl (tbl_ok : table_ok tfibsegs tbl) W n stop E ss ss' st ms STK sp0 FP ly S W0 mem
  md own lyc Sc U mdc k Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sym_run_toN tfibsegs tbl n stop ss = (ss', st) ->
  match st with RS_ecall => False | _ => True end ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) ->
  run_post_AJU B W E ss ss' ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros B tbl tbl_ok W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q HS Hrun Hst HARU HJ Hwr Hk.
destruct (msteps_run_to_gen tfibsegs tbl tbl_ok n stop E ss ss' st _ HS Hrun) as (msr' & Hms & HS' & Hfr).
eapply fsw_chain_AJU.
all: first [ solve [exact Hms] | solve [exact Hfr] | solve [exact HARU] | solve [exact HJ] | solve [exact Hwr]
           | solve [exact Hk] | solve [destruct st; [exact HS' | destruct Hst | exact HS']] ].
Qed.
Lemma fsw_chain_tok_AJU : forall B W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q,
  msteps tfibsegs (restrict (w_H W) ms) msr' ->
  length ws = sh_j st' ->
  st_ok tfibsegs (extK E K ws) (sh_ss st') msr' ->
  sh_ok tfibsegs Bx SH (extK E K ws) (ms_mem msr') ->
  frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) ->
  run_post_tok_AJU B W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros B W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q Hms Hlen HS' Hsh' Hfr HARU HJ
  Hwr Hk.
apply (SRr_msteps tfibsegs fs_wx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows tfibsegs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
destruct (fsw_exec_U B W E ss ms msr' STK sp0 FP ly S W0 mem md own lyc Sc U mdc k model' HJ HARU Hwr Hfr Hgr Hcl Hsame)
  as [HJ' HARU'].
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- exact HJ'.
- exact HARU'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma fsw_run_tok_AJU : forall B tbl (tbl_ok : table_ok tfibsegs tbl) W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S
  W0 mem md own lyc Sc U mdc k Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sh_ok tfibsegs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_runN_tok tfibsegs tbl K Bx Bspan SH n ss = (st', r) ->
  match r with TS_ecall => False | _ => True end ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  Forall (ob_holds tfibsegs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) ->
  run_post_tok_AJU B W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros B tbl tbl_ok W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q
  HS Hsh Hchk Hrun Hr HARU HJ Hobl Hwr Hk.
destruct (sym_run_tok_sound tfibsegs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
  as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply fsw_chain_tok_AJU.
all: first [ solve [exact Hms] | solve [exact Hlen] | solve [exact Hsh'] | solve [exact Hfr] | solve [exact HARU]
           | solve [exact HJ] | solve [exact Hwr] | solve [exact Hk]
           | solve [destruct r; [exact HS' | destruct Hr | exact HS']] ].
Qed.
Lemma fsw_run_to_tok_AJU : forall B tbl (tbl_ok : table_ok tfibsegs tbl) W n stop E K Bx Bspan SH ss st' r ms STK sp0
  FP ly S W0 mem md own lyc Sc U mdc k Q,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sh_ok tfibsegs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
  sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  sym_run_toN_tok tfibsegs tbl K Bx Bspan SH n stop ss = (st', r) ->
  match r with TS_ecall => False | _ => True end ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdc ->
  ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W (unpoison U (ms_mem ms)) mdc k ->
  Forall (ob_holds tfibsegs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
  awr_ok tfibsegs B E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) ->
  run_post_tok_AJU B W E K Bx SH ss st' ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q ->
  SRr tfibsegs W (mkCfg ms mdc) Q.
Proof.
intros B tbl tbl_ok W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S W0 mem md own lyc Sc U mdc k Q
  HS Hsh Hchk Hrun Hr HARU HJ Hobl Hwr Hk.
destruct (sym_run_to_tok_sound tfibsegs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
  as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply fsw_chain_tok_AJU.
all: first [ solve [exact Hms] | solve [exact Hlen] | solve [exact Hsh'] | solve [exact Hfr] | solve [exact HARU]
           | solve [exact HJ] | solve [exact Hwr] | solve [exact Hk]
           | solve [destruct r; [exact HS' | destruct Hr | exact HS']] ].
Qed.
End r.
(* the per-register goals of fsw_preserved after one program call: expectf gives the expected symbolic value
   (sp back up by the frame, reloaded extra atoms, or the entry atom kept across the call);
   HSc is the call-site state, HP the callee's aregs_preserved, Esp the resumed sp *)
Ltac fsw_cs_cases expectf HSc HP Esp :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv [CALLEE_SAVED In] in Hr;
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (expectf ?q) = _ =>
    let e := eval vm_compute in (expectf q) in change (expectf q) with e end;
  first
  [ eapply fsw_sp_back; rewrite Esp; lia
  | rewrite fsw_SOff0; reflexivity
  | eapply fsw_kept_reg;
    first
    [ solve [exact HSc]
    | solve [exact HP]
    | lazymatch goal with |- sr_get _ _ = _ => solve [vm_compute; reflexivity] end
    | lazymatch goal with |- Z.of_nat _ = _ => solve [vm_compute; reflexivity] end
    | lazymatch goal with |- acallee_saved _ =>
        solve [unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
          let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia] end ] ].
(* the write-window obligation of a run resumed after a call (one stack region, base sp0 - f, window [0, f)) *)
Ltac fsw_awr_ret Esp f :=
  try (unfold fss_ret); cbn [add_cond ss_mem];
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - f);
  first [ lazymatch goal with |- _ = Some _ => solve [reflexivity] end
        | lazymatch goal with |- bv_unsigned _ = _ => solve [exact Esp] end
        | lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => solve [apply awr_ok_nil] end
        | lazymatch goal with |- _ <= _ => solve [cbn; lia] end ].
(* every unrestricted run frame in context (one stack region at or above alloc_ceiling) as same_below, chained *)
Ltac fsw_sb Esp :=
  repeat match goal with
  | HF : frame_of ?E ?rs ?m1 ?m2 |- _ =>
      lazymatch m1 with mrestrict _ _ => fail | _ => idtac end;
      let H := fresh "SB" in
      assert (H : same_below m1 m2 alloc_ceiling)
        by (try (unfold fss_ret in HF); cbn [add_cond ss_mem] in HF;
            eapply (same_below_frame1 E _ m1 m2 alloc_ceiling HF);
            first [ solve [cbn [YP09.r_base YP09.r_wlo base_val fstk_ret]; rewrite Esp; lia] | solve [lia] ]);
      clear HF
  end;
  repeat match goal with
  | H1 : same_below ?a ?b alloc_ceiling, H2 : same_below ?b ?c alloc_ceiling |- _ =>
      let H := fresh "SB" in pose proof (same_below_trans a b c alloc_ceiling H1 H2) as H; clear H1 H2
  end.
(* the return of a framed function after one program call: everything of fpost (U = []) but its Q *)
Ltac fsw_ret tblok expectf HSf HJf HSc HP Esp Hra LAWS HSL :=
  lazymatch type of HSf with st_ok _ (Ereg ?regs2 ?extra) ?ssf (restrict (w_H ?W2) ?msf) =>
  let R1F := fresh "R1F" in
  pose proof (fsw_reg_extra _ regs2 extra _ msf 1%bv 0 HSf ltac:(vm_compute; reflexivity)) as R1F;
  eapply (SRr_ret_at tfibsegs _ tblok fs_wx);
  first [ solve [exact HSf]
        | lazymatch goal with |- ss_resv _ = _ => solve [reflexivity] end
        | lazymatch goal with |- clookup _ _ = _ => solve [vm_compute; reflexivity] end
        | lazymatch goal with |- forall _, _ => idtac end ];
  let mat2 := fresh "mat" in intros mat2;
  let Hpc := fresh "Hpc" in
  lazymatch type of Hra with YK0s.ret_ok (getr ?regs0 1) =>
    assert (Hpc : v_jalr (getr (ms_regs msf) 1) 0 = getr regs0 1) by (rewrite R1F; exact Hra);
    rewrite Hpc; unfold fpost, apost_base;
    rewrite ?wvb_collapse in HJf;
    do 5 eexists; split; [reflexivity|];
    split; [apply (ajournal_materialize tfibsegs _ LAWS HSL); exact HJf|];
    split; [apply (fsw_preserved _ _ _ msf regs0 expectf HSf); [vm_compute; reflexivity | fsw_cs_cases expectf HSc HP Esp]|]
  end end.
(* ---- U form run tactics: the donor's aj_run / aj_run_to / aj_run_tok / aj_run_to_tok (YCbq.v) over fsw_*_AJU. HJ is the
   journal over the unpoisoned memory, HARU the ARU of the machine's memory at the run's start; both come back, under
   the same names, for the memory at the run's end ---- *)
Ltac fsw_aj_after_runU HS HJ HARU :=
  let ms' := fresh "ms" in let mat' := fresh "mat" in
  let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
  intros ms' mat' HS HJ HARU HF HFr HG;
  cbn [ms_mem mkst] in HF, HFr, HG, HJ, HARU;
  try match type of HS with context [restrict _ ?msn] =>
    repeat match goal with
    | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
    end
  end;
  srr_norm_model.
Ltac fsw_aj_runU tblok HS HJ HARU :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        eapply (fsw_run_AJU _ tbl tblok W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HARU HJ);
        first
        [ lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => clear Hrun end
        | lazymatch goal with |- run_post_AJU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
            clear Hrun HS HJ HARU; fsw_aj_after_runU HS HJ HARU end ]
      end
    end
  | _ => fail "fsw_aj_runU: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
  end.
Ltac fsw_aj_run_toU tblok HS HJ HARU stop :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_run_toN segs tbl FUEL stop ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN segs tbl FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
        eapply (fsw_run_to_AJU _ tbl tblok W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HARU HJ);
        first
        [ lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => clear Hrun end
        | lazymatch goal with |- run_post_AJU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
            clear Hrun HS HJ HARU; cbv beta iota; fsw_aj_after_runU HS HJ HARU end ]
      end
    end
  | _ => fail "fsw_aj_run_toU: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
  end.
Ltac fsw_aj_after_run_tokU HS HJ HARU SHOK :=
  let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
  let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
  intros ws ms' mat' Hlen HS SHOK HJ HARU HF HFr HG;
  cbn [sh_j sh_ss] in Hlen, HS, SHOK;
  repeat (let w := fresh "w" in
    destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
  (destruct ws; [clear Hlen | discriminate Hlen]);
  cbn [extK] in HS, SHOK;
  cbn [ms_mem mkst] in HF, HFr, HG, HJ, HARU;
  try match type of HS with context [restrict _ ?msn] =>
    repeat match goal with
    | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
    end
  end;
  srr_norm_model.
(* the tok runs' SK: the walk's Section may carry no  {SK : YI16.sink_head}  Context (the walks pass SK on), so
   fsw_run_tok_AJU's SK cannot be left to instance resolution; take it (with rc) from the journal hypothesis HJ *)
Ltac fsw_aj_run_tokU tblok HS HJ HARU SHOK Bspan :=
  lazymatch type of HJ with
  | @ajournal ?rcj ?skj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    lazymatch type of HS with
    | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
      lazymatch type of SHOK with
      | sh_ok _ ?Bx ?SH _ _ =>
        lazymatch type of tblok with
        | table_ok _ ?tbl =>
          let K := eval vm_compute in (run_K 0 Bx SH ss) in
          let r := eval vm_compute in (sym_runN_tok segs tbl K Bx Bspan SH FUEL ss) in
          lazymatch r with
          | (?st', ?rs) =>
            let Hrun := fresh "Hrun" in
            assert (Hrun : sym_runN_tok segs tbl K Bx Bspan SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
            eapply (@fsw_run_tok_AJU _ rcj skj _ tbl tblok W FUEL E K Bx Bspan SH ss st' rs ms
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK ltac:(vm_compute; reflexivity) Hrun I HARU HJ);
            first
            [ lazymatch goal with |- Forall _ _ => clear Hrun; cbn [sh_obls]; srr_obls end
            | lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => clear Hrun end
            | lazymatch goal with |- run_post_tok_AJU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                clear Hrun HS HJ HARU SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
                fsw_aj_after_run_tokU HS HJ HARU SHOK end ]
          end
        end end
    | _ => fail "fsw_aj_run_tokU: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
    end
  | _ => fail "fsw_aj_run_tokU: HJ must be an  ajournal  hypothesis"
  end.
Ltac fsw_aj_run_to_tokU tblok HS HJ HARU SHOK Bspan stop :=
  lazymatch type of HJ with
  | @ajournal ?rcj ?skj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    lazymatch type of HS with
    | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
      lazymatch type of SHOK with
      | sh_ok _ ?Bx ?SH _ _ =>
        lazymatch type of tblok with
        | table_ok _ ?tbl =>
          let K := eval vm_compute in (run_K 0 Bx SH ss) in
          let r := eval vm_compute in (sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss) in
          lazymatch r with
          | (?st', ?rs) =>
            let Hrun := fresh "Hrun" in
            assert (Hrun : sym_run_toN_tok segs tbl K Bx Bspan SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
            eapply (@fsw_run_to_tok_AJU _ rcj skj _ tbl tblok W FUEL stop E K Bx Bspan SH ss st' rs ms
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK ltac:(vm_compute; reflexivity) Hrun I HARU HJ);
            first
            [ lazymatch goal with |- Forall _ _ => clear Hrun; cbn [sh_obls]; srr_obls end
            | lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ => clear Hrun end
            | lazymatch goal with |- run_post_tok_AJU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
                clear Hrun HS HJ HARU SHOK; try match type of ms with machine_state => clear ms | _ => idtac end;
                fsw_aj_after_run_tokU HS HJ HARU SHOK end ]
          end
        end end
    | _ => fail "fsw_aj_run_to_tokU: HS must be  st_ok segs E ss (restrict (w_H W) ms)"
    end
  | _ => fail "fsw_aj_run_to_tokU: HJ must be an  ajournal  hypothesis"
  end.
