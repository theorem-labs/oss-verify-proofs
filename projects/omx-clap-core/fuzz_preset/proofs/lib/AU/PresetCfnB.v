(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from tfib_lib_contract_x of proofs/cgif/cgif_file_fuzzer/lib/YCfn.v and its
   asan twin lib/A/ACfn.v, for fuzz_preset. This file (asan-ubsan) and lib/A/PresetCfnA.v (asan) are the same text
   except for the Requires of the segment list and of the image's generated facts, and the image values of section 1.
   It states the PROGRAM INTERFACE of fuzz_preset's LLVMFuzzerTestOneInput on the ASan side: the contract the harness
   walk proves and the closed walk consumes. Nothing in this file is a proof of a function (rule 24).
   Changes from the donor:
   (1) every allocator predicate is over preset's SECOND allocator instance (h-mani-a8's ARcf, lib/Reusable/YG0ncf.v),
       never cgif's AR. The per-function frame names afn_pre_cf / ajournal_cf / apost_base_cf / ablocks_cf are
       ABBREVIATIONS (section 4, a Theorem Labs lane's plan): lib/Reusable/YCbqG.v's afn_pre_x / ajournal_x / apost_base_x
       (the journal of record, blob 83da015952be, from the engine fold origin/cold/c-omx-alloc-preset-s1
       63997a07aa64) at ARx := ARcf segs B and PST := K0's prh_pst (the seven
       harness statics), and cgif's ablocks (lib/Reusable/YG0d.v:433), never cgif's YCbq afn_pre / ajournal. The
       float post cites YCbqG's fregs_kept_x;
   (2) cgif's event room `st_nev S + EV_LIB <= EV_MAX` is gone, with no allowance in its place: a8's LIB_ROOM over the
       live-state credit abudget_cf and the ceiling CF_MAX holds at every allowance m <= 2 ^ 36 from the pre's own
       instance invariant (lib_room_of_wf, section 3). The allocator's room is two STATE conjuncts (section 3b), never a count
       of allocator steps: iface_room_at, the premises of c-frame-alloc's P8 (lib/Spec/PresetP8.v preset_room,
       origin/cold/c-frame-alloc-p8 4ec915e66b6) at the harness entry, from which every consumer allocation of the
       model run (PresetRun.hruns) finds a free slot of its primary class (iface_room_at_entry, below), so a
       primary malloc_cf there returns NULL only on an environment refusal (preset_no_refusal, P8's no_null_preset,
       under the walk's named premise run_allocs_follow); and
       iface_room_np, the NON-primary room (secondary count, error buffer, batch-class map: what a8's ROOM_cf_k
       measures and P8 does not), a PROVISIONAL Section variable; the seam instantiates it at a Theorem Labs lane's state-restored form room_live_cf;
       the float state: the pre takes frm_zero of the entry fcsr, and the return config's float state is an
       existential fx' with frm_zero and the callee-saved f registers kept (apost_base_xF's form), since callees
       reach musl strtod;
   (3) cgif's sink family (asink_none, ameta_inv, the free fd, the sink token footprint) and its write callback are
       dropped: preset's entry function opens no file and has no function pointer (its only jalr are the switch
       jumps of tx_value and write_value);
   (4) NEW: PINV, the cross-call invariant that replaces cgif's FINV (lib/Reusable/YD1u.v:67-70): the alloc.c ledger
       at rest and the musl stdio cells, with its frame lemmas and its bridge to K0's alloc.c ledger (PRH_Base
       prh_ledger at an empty block list, both directions). g_ran_out is ONE byte in both images (the compiler
       shrinks `static int g_ran_out`; a Theorem Labs lane's note, the internal file RANOUT-WIDTH.md), so PINV reads one byte;
   (5) NEW: PAYLOAD_ROOM, the payload-level room that the agreement's plain no-refusal premise yields, and a8's
       xs_placed_cf (the errbuf slot placed like a live secondary) as a conjunct of the pre and of the post;
   (6) NEW: the callee contracts of the entry function, one per callee, in place of cgif's three library contracts;
       on the #102 pins they are sixteen (nine program functions, then seven alloc.c accessors) and the frame pair;
       fi_fp reads the entry memory, because pj_free's footprint is the freed tree's blocks, which only memory fixes;
       the decision was made at 11:48Z;
   (7) NAMED PREMISE, empty frame chain: the interface's afn_pre passes ch = [] (no caller frame for the ASan fast
       unwinder to walk), which is achain's first disjunct (lib/Reusable/YCbq.v:218-224). The pre states the bound it
       is taken under, `s0Z regs < YM05.alloc_ceiling` (achain_low), never the `ly_top ly - 16 <= s0` disjunct. It holds at
       the entry: target_run moves its 4th argument a3, the payload length n, into s0 at its entry (on the #102 pins
       `mv s0, a3` at asan 0x81438, asan-ubsan 0x81524) and writes s0 no more before its jal to the entry function
       (0x814d8 / 0x815c4; capstone over the twins), so
       s0 = n < 2 ^ 26 < CEIL_MIN = 0x7fff7f800000 <= YM05.alloc_ceiling (YM05.v:11, :19; the donor's driver proves
       the same fact at this call, lib/Reusable/YD1r.v:618 and YD1w.v:78). The entry function's own call tree does allocate, free and unwind;
       what this premise says is only that the walk stops at the entry function's frame.
   (8) NEW, memnorm (h-hpreset-7's ruling 10:04Z, spelling 11:15Z): the pre takes YAkMemnorm.memnorm segs mem
       (lib/Reusable/YAkMemnorm.v:41, blob 96c72061b4d4, an engine file over LPS only: the body of
       Lib.Mem.mem_inv segs m /\ MemNorm.task_mem segs m, written without lib/Lib) over the call configuration's FULL
       overlay mem, the same term and the same memory K0's texts take as their entry premise (strtod's row consumes
       it), and the post gives it on the return configuration's full overlay mem'. memnorm is seeded at main (both images, proved:
       A/AjMemnormMainA.v, B lib/Reusable/YjMemnormMainB.v), kept across calls (PRH_Base.fpostm), and kept across
       runner segments: callers supply it through the named premise H_memnorm_drv_B, PROVED by PresetD1rBmn's
       H_memnorm_drv_B_holds (YSRrMemnorm.srr_inv_laws_memnorm_k, over YC80x.SRr_msteps_inv). The at-main seeds conclude over FULL, `YAjMemnorm.memnorm TSEGS FULL` (a working branch
       53164b435dc): A/AjMemnormMainA.v tfib_memnorm_at_main (blob 70373baab984) and lib/Reusable/YjMemnormMainB.v
       tfib_memnorm_at_main_B (blob 89990de73a3b). They conclude YAjMemnorm.memnorm; the one conversion at that seam is
       YAkMemnormJ.memnorm_kit_j (lib/Reusable/YAkMemnormJ.v, blob f6dbdc03064b; the two bodies are convertible, its
       proof is `exact`), which only a leaf may Require.
   (9) NEW, the callees' float state (h-hpreset-7 10:1xZ): afn_spec_cf takes frm_zero of the entry fcsr and posts in
       apost_base_cfF (YCbqG.apost_base_xF's form): the rounding mode is 0 again and the callee-saved registers fs0-fs11
       are kept. It does NOT claim that the argument / temporary f registers (fa0-fa7, ft0-ft11) or the accrued flags
       (fflags) are kept: after a callee they are FREE. preset_callee_contracts holds at every float state
       (preset_lib_x_stmt quantifies it over fx), so the walk has each callee's contract at the float state the
       previous callee returned in.
   (10) #102 PINS (harness fix #102; pins asan 1be0f53d, asan-ubsan d663f82d; LlvmWalk's need, port/llvm-iface-need.md):
       section 1's values are re-measured and RA_LLVMF moved; the entry function and its sixteen callees are the listing
       class's pa_sigma (section 4); the callee record and preset_lib_x_stmt list the sixteen; PINV reads g_most and
       g_own_ran_out too; the seam is iface_seam_segs (conversion) and the room bridge is iface_room_post_of_pos_end.
   (12) D1 / D2 (owner 17:34Z): the sixteen callee contracts ARE K0's t<f>_specX texts (section 6, at iface_ctx0 =
       [[RA_LLVMF]], ARx := ARcf /\ xs_placed_cf, prh_room_live_a8, check_round_trip's literals A_MOD_AT / A_STAMP as
       arguments of preset_lib_x_stmt); the donor's fn_iface / afn_spec_cf schema left the slot; the pre's universe is at
       iface_ctx0; and the pre carries the count headroom cnt + LCNT < 2 ^ 62 - 2 ^ 30, which the DRIVER proves at the
       slot call (never a premise of the top).
   (11) NEW (#102, LlvmWalk's section 5): (a) pcc_stack_malloc is the MEMNORM-KEEPING frame call
       astack_malloc_realizes_cfm (the engine's YGcallMxmn.astack_malloc_realizes_xm at ARcf); (b) the pre's NEXT-TO-LAST
       conjunct (item (13)'s is last) is the kit's prh_univ_closure B iface_ctx0 (D1: the top's own entry context [[RA_LLVMF]]).
       NO run data words (owner 22:03Z, the kit's batch): clause 4 is the fixed code word (4a) or inU of the instance universe
       (4b), so the slot pre has no DW and no payload-end membership. WHO SUPPLIES (b) at the top: the instance's as_universe
       (a Theorem Labs lane's A generator, provenance/gen_prh_img.py's GATE; a Theorem Labs lane's UniverseB for image B; a Theorem Labs lane's
       univcore Univ / inU / admits).
       DRIVER FRAMES (the kit owner's note, 22:30Z): the driver supplies presence of the driver frames [sp, sp + 208) at
       every LIB call (spZ regs = usp - 208; lib/AU/PresetD1rBPf.v calls_loop_cf's Hwin :449-453, from lib/Reusable/YD26.v:75
       / YD27.v:455 / YD25.v:194), and the pre's LAST conjunct asks it: item (13)'s astack_up_x, presence of [sp, ly_top)
       (lib/Reusable/YGcallStackUp.v:59-60), which tcheck_round_trip_specX takes (lib/A/PRH_FnCheck.v:2392).
   (12) NEW (#102): afn_spec_cf no longer takes `blocks_bytes S + LIVE_LIB <= LIVE_MAX`. Every callee
       record that allocates states its K0 text's own live premise in fi_pre (`blocks_bytes S + LIVE_<name> .. <=
       LIVE_MAX`, h-rw-pre-7's PRW_AfnBridgeBProg records), so the callee contract is stronger and no bridge used the
       premise (all three introduce it as `_`). The pre keeps its LIVE_LIB bound (section 2). The pre's
       `LIB_ROOM abudget_cf CF_LIB S` and the constant CF_LIB are gone: lib_room_of_wf gives LIB_ROOM m for every
       m <= 2 ^ 36 from afn_pre_cf's ARcf and qtight.
   (13) NEW (2026-10-30; a Theorem Labs lane's chain ruling 09:23Z, after a Theorem Labs lane's ruling 10:58Z on
       PRH_FnCheck.tround_trip_text_specX): the pre's LAST conjunct is `YGcallStackUp.astack_up_x segs ly W (spZ regs)
       mem`, the live real stack [sp, ly_top) present at the slot call (a Theorem Labs lane's engine leaf,
       lib/Reusable/YGcallStackUp.v). It is UNGUARDED. The GUARDED twin `spZ regs <= pa -> astack_up_x ..` of
       PRH_FnEx.tsame_specX (PRH_FnEx.v:375) is a DIFFERENT statement; do not read one for the other. It is the top of
       the chain round_trip_text -> check_round_trip -> LLVMFuzzerTestOneInput, each text with the same conjunct
       appended last (PRH_FnCheck.v tround_trip_text_specX, tcheck_round_trip_specX); evidence that it is met at the
       real call state given check_round_trip's entry fact: the check_round_trip walks prove it by YGcallStackUp.astack_up_at_xwR at Crt102Arms.v:1102-1109 and Crt102B_RRT.v:1096-1101. Appended,
       so a positional destruct of the pre that ends in `_` is unchanged. The DRIVER gives it at every slot call from its
       invariant astack_up_x at usp (lib/AU/PresetD1rBPf.v calls_loop_cf, premise :417, conjunct :461-462); the invariant's
       root at main is lib/AU/PresetD1pBPfC.v:62 H_stackup_main_B_holds (Qed, by StackUpMainB.stack_up_main_W1_B).
       BINDERS: the conjunct's text is PRH_FnCheck.v's, but this pre binds `(regs ly S Hp W mem md ..)` in that
       order, where PRH_FnCheck's texts bind `forall ly S Hp W regs mem md ..`; and `segs` here is this file's
       `Local Notation segs := tfibsegs` (section 4), NOT the callee texts' pa_segs. A walk that hands the conjunct
       to tcheck_round_trip_specX moves it across the iface_seam_segs seam (section 1), as it does memnorm.
   (14) NEW (2026-10-31): THE SLOT OVER A WORLD RELATION. The free and realloc contracts move to posts that re-hide
       shadow (lib/Reusable/YGcfRehidePost.v), whose world step is not wle, so the walk of LLVMFuzzerTestOneInput
       reaches its return at YA0nH.wle' (the hidden set grows only inside YGcfRehidePost.RZ_cf), not at wle. Beside
       each plain form there is an R form over a world relation R (YCbqG.v's pattern): ajournal_cfwR
       (YCbqG.ajournal_xwR; R after the instance arguments sg B, as there), preset_lib_post_xR (the journal at
       ajournal_cfwR R) and preset_lib_contract_xR (`R W W'` at the continuation's world step, preset_lib_post_xR R in
       its post), R the first binder of the two slot texts. Each R body is a COPY of its plain body, and the plain
       bodies stay (their importers destruct them); ajournal_cfw_R_wle, preset_lib_post_x_R_wle and
       preset_lib_contract_x_R_wle (by reflexivity) check that each plain form IS its R form at wle, so the copies
       cannot drift. The walk's slot preset_lib_x_stmt and the program slot preset_lib_contract_x_all are stated at
       R := YA0nH.wle' segs RZ_cf.
   LIA-CLEAN: NO. `Ltac lia ::=` (lib/Lib/LiaTwx2.v, lib/CJ/Lib/LiaTuning.v) is in this file's Require closure through
   the kit and P8, not through memnorm (each arrow: Requires):
     PRH_Base / PRH_Img -> Prog/Ledger -> Contract -> Lib/Exec -> Lib/PropExec -> Lib/LiaTwx2;
     Spec/PresetP8, PresetSite17, PresetGate, PresetLiveSec, A/CfRoomLivePreset -> Prog/PjWriteHyp -> Lib/Frame ->
       Lib/PropExec -> Lib/LiaTwx2, and Prog/PjWriteHyp -> Prog/ReaderRes -> Prog/strtod_c -> CJ/Spec/FloatScan ->
       CJ/Lib/FP -> CJ/Lib/PropExec -> CJ/Lib/LiaTuning.
   Measured by a comment-stripped scan of the build's .Makefile.d closure (286 files for asan, 284 for asan-ubsan),
   2026-10-29. Cuts, if ever needed: Prog/Ledger (K0), Prog/PjWriteHyp (c-frame-alloc / h-hpreset-7).
   The library shape stays generic (LS), as in the donor; the composition fixes it at ZTraceSpec.checksum_shape, and
   libk_has_nil (end of file) is the one lemma that replaces cgif's ff_unl_has_nil / ff_libk_has_nil there.
   PROVISIONAL (harness re-pin): every literal of section 1 except RA_LLVMF, the estimates of section 2, and the
   callee contracts of section 6 depend on preset's harness code, which is being changed at six NULL sites;
   regenerate them on the new pins. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG01cf YG0dcf YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Base CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PRH_ImgB.
(* the sixteen callee texts of the #102 slot are a Theorem Labs lane's (D1, owner 17:34Z): lib/A/PRH_FnAlloc.v, PRH_FnPj.v, PRH_FnCheck.v *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc PRH_FnPj PRH_FnCheck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
(* The journal layer (the engine fold's YCbqG), the instance's room and free-history files (h-mani-a8), and P8's model
   and room theorem (lib/Spec, by path from origin/cold/c-frame-alloc-p8 4ec915e66b6). All used qualified. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqG YG00cf YGcfRoom YGcfFrees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoom PresetReqAt PresetRun PresetRunQ PresetSite17.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetP8.
(* the instance's chunk geometry (h-mani-a8), for preset_lib_pre_pay8; used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0s YG0scf.
(* the live-set counts at a position of the run: the leaf lib/Spec/PresetRoomCounts.v (moved out of this file so that
   citing them does not pull this file's plain-image closure); used qualified, not re-exported *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts.
(* iface_room_pos's one home, the leaf lib/Spec/PresetRoomPos.v (re-exported in section 3b) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
(* the seam's segment list (section 1, iface_seam_segs) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Img0.
(* memnorm, the overlay normal form (header item (8)), over LPS only (no lib/Lib, so no LiaTwx2 `lia` override);
   used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
(* the per-LIB-call wild budget K_LLVMF := 140 is a Theorem Labs lane's, in the image-free engine leaf YCbqGwild.v (here at
   a working branch 5dfea14535d2's blob 134630095988; the batch kit's head carries c-omx-alloc-univwiden's
   aa0b10a819fa, the same K_LLVMF), cited; its witnesses (lib/A/WildRoomInstA.v wild_room_init_A / wild_room_run_fits_A,
   lib/AU/WildRoomInstB.v the _B twins) apply by conversion at the concrete TfibB only. On the batch kit's head the per-call
   need is proved: prh_wk and WildBudget.lib_wild_budget (<= K_LLVMF) *)
(* the engine's memnorm-keeping frame call (section 6, pcc_stack_malloc; s1b's YGcallMxmn.v); used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
(* the slot's world relation (section 5, header item (14)): YA0nH.wle' at YGcfRehidePost.RZ_cf; used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YGcfRehidePost.
(* IMPLICIT-INSTANCE GUARD (c-omx-hpreset 22:57Z; template fuzz_state S0 bffd3c8f802, lib/A/FSH_Harness.v:27-32 and
   FSH_Gen.v:28-49). Every walk of image B imports this harness contract. Reusable/YE2k.v:37 `#[export] Instance tfib_sink_head`
   carries image B's musl ofl_head (YE2k's A_ofl_head: 0x5fe888, YE2k.v:30 at origin/cold/h-mani-a4-preset-relocB
   6e96e6221c3a), and the cgif harness library files this unit keeps Import it; Reusable/
   YI5b.v:12 `#[global] Instance src0_sink_head` carries the PLAIN build's. A site that leaves SK to inference would
   get one of them: the wrong image, green and vacuous. Both are removed here, #[global] so the removal holds
   wherever this file is loaded; the two files are Required only to name the instances. Caveat: an explicit
   `Import YE2k` AFTER this file re-activates its export instance in that file, so every site passes SK with `@`.
   The U chain's YI5b instance is of a different class (U/Reusable/YI16.v) and is not removed.
   The same holds for the PLAIN build's sink symbols: Reusable/YI5c.v:15 `#[global] Instance src0_sink` (class
   YI14.sink_syms) and :38 `src0_sink_laws` (class YI14.sink_laws) are removed too (a Theorem Labs lane's sink audit F2).
   The three Fail lines below check that no instance of the two sink classes is left; the last one states the type
   of src0_sink_laws itself, so that it fails only on the instance search. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YI5c.
#[global] Remove Hints YE2k.tfib_sink_head : typeclass_instances.
#[global] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[global] Remove Hints YI5c.src0_sink YI5c.src0_sink_laws : typeclass_instances.
Fail Definition iface_guard_sink_head : YI16.sink_head := _.
Fail Definition iface_guard_sink_syms : YI14.sink_syms := _.
Fail Definition iface_guard_sink_laws : ltac:(let T := type of YI5c.src0_sink_laws in exact T) := _.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 1. Image literals, on the FIXED harness (#102). MEASURED on bin fuzz_preset.asan 1be0f53d / fuzz_preset.asan-ubsan
      d663f82d through their unstripped twins bff8519b / c90d4fa5 (reports/preset-harness/bound-fix/9e1283d1,
      SHA256SUMS; symbol table and capstone, 2026-10-29); values as asan / asan-ubsan, this file's image B:
      A_LLVMF        LLVMFuzzerTestOneInput                         0x815e0  / 0x816cc  generated: pa_sigma (section 4)
      RA_LLVMF       target_run's `jal LLVMFuzzerTestOneInput` + 4  0x814dc  / 0x815c8  (jal at 0x814d8 / 0x815c4)
      A_EMPTY        oft_aligned_copy.empty                         0x5dd520 / 0x5ddd60
      G_RAN_OUT      g_ran_out (ONE byte in the image)              0x5dd5c0 / 0x5dde00 generated: pi_g_ran_out
      G_LIVE         g_live (size_t)                                0x5dd560 / 0x5ddda0 generated: pi_g_live
      G_PEAK         g_peak (size_t)                                0x5dd580 / 0x5dddc0 generated: pi_g_peak
      G_COUNT        g_count (size_t)                               0x5dd5a0 / 0x5ddde0 generated: pi_g_count
      G_FAIL_AT      g_fail_at (size_t, .data, image bytes ff..ff)  0xa65c0  / 0xa6e00  generated: pi_g_fail
      G_MOST         g_most (size_t, .data, image value SIZE_MAX)   0xa65e0  / 0xa6e20  generated: pi_g_most (NEW)
      G_OWN_RAN_OUT  g_own_ran_out (fuzz_preset.c, ONE byte)        0x5dd540 / 0x5ddd80 generated: pi_g_own_ran_out (NEW)
      A_THREADED     __libc + 1 (musl's __libc.threaded)            0x5fe181 / 0x5fe9c1 (__libc 0x5fe180 / 0x5fe9c0)
      A_NEED_LOCKS   __libc + 3 (musl's __libc.need_locks)          0x5fe183 / 0x5fe9c3
      A_OFL_LOCK     ofl_lock (int)                                 0x5fe5e0 / 0x5fee20
      A_OFL_HEAD     ofl_head (FILE * )                             0x5fe5e8 / 0x5fee28
      The alloc.c cells, g_own_ran_out and the stdio cells are .bss (zero in the image), except g_fail_at and g_most
      (.data, SIZE_MAX). Each harness static has symbol size 32 because ASan pads a global with its redzone; the datum
      is its first 8 bytes (1 for g_ran_out and g_own_ran_out, their __asan_global records' size; their accesses are
      lbu / sb). RA_LLVMF MOVED with the driver block (old 0x81448 / 0x814cc).
      GENERATED NAMES, never retyped where a generated file has one. The seven harness statics come from the
      generated PrhImg (lib/B/PRH_ImgB.v prh_img_B 3216eca68342, commit 1bba49fd7ac5;
      generator provenance/gen_prh_img.py 6f17b81ee32316bf) through preset_prh_img. The entry function and its
      sixteen callees are the listing class's pa_sigma (section 4): a Theorem Labs lane's re-emitted listing
      (origin/cold/h-verbs-1-listing-pins102 d42e123915ae, lib/B/PAImg_prog.v 4392ab2c09ba (lemmas B_entry_<name>)) gives their values at
      PA := PI_prog_B. RA_LLVMF, A_EMPTY and the four stdio cells have no generated name on the #102 pins: they are
      typed constants, each with its source on its line. *)
Definition RA_LLVMF : Z := 0x815c8. (* MEASURED, no generated name: twin c90d4fa5, target_run's jal at 0x815c4 *)
Definition A_EMPTY : Z := 0x5ddd60. (* MEASURED, no generated name: twin c90d4fa5, symbol oft_aligned_copy.empty *)
Definition preset_prh_img : PRH_Base.PrhImg := PRH_ImgB.prh_img_B. (* generated *)
Definition G_RAN_OUT : Z := @PRH_Base.pi_g_ran_out preset_prh_img. (* generated *)
Definition G_LIVE : Z := @PRH_Base.pi_g_live preset_prh_img. (* generated *)
Definition G_PEAK : Z := @PRH_Base.pi_g_peak preset_prh_img. (* generated *)
Definition G_COUNT : Z := @PRH_Base.pi_g_count preset_prh_img. (* generated *)
Definition G_FAIL_AT : Z := @PRH_Base.pi_g_fail preset_prh_img. (* generated *)
Definition G_MOST : Z := @PRH_Base.pi_g_most preset_prh_img. (* generated *)
Definition G_OWN_RAN_OUT : Z := @PRH_Base.pi_g_own_ran_out preset_prh_img. (* generated *)
Definition A_THREADED : Z := 0x5fe9c1. (* MEASURED, no generated name: twin c90d4fa5, __libc 0x5fe9c0 + 1 *)
Definition A_NEED_LOCKS : Z := 0x5fe9c3. (* MEASURED, no generated name: twin c90d4fa5, __libc 0x5fe9c0 + 3 *)
Definition A_OFL_LOCK : Z := 0x5fee20. (* MEASURED, no generated name: twin c90d4fa5, symbol ofl_lock *)
Definition A_OFL_HEAD : Z := 0x5fee28. (* MEASURED, no generated name: twin c90d4fa5, symbol ofl_head *)
(* the sink head YCbqG's journal reads under fp_spares: this image's ofl_head, passed explicitly (sections 4 and 6) *)
Definition preset_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := A_OFL_HEAD |}.
(* THE SEAM (#102, section 4): this interface is stated over tfibsegs (lib/Reusable/YB1v.v:14, AsanUbsan.M.loaded_segments). The
   listing class's instance PI_prog_B (lib/B/PAImg_prog.v) has pa_segs := Img0.rsegs, and Img0.rsegs is the same
   AsanUbsan.M.loaded_segments (lib/B/Img0.v), so `@pa_segs rc L PI_prog_B = tfibsegs` holds BY CONVERSION (eq_refl) on any
   facts tree; the half that does not import the image is checked here. *)
Lemma iface_seam_segs : Img0.rsegs = tfibsegs.
Proof. reflexivity. Qed.
(* The direct callees of LLVMFuzzerTestOneInput on the #102 pins (capstone over the twins: every `jal` whose target is
   outside the function, 19 sites, 17 distinct callees; there is no jalr in it). Calls per run in brackets; their
   entries are pa_sigma AS_<name> (section 4). read_members is out of line now, and LLVMFuzzerTestOneInput calls
   neither pj_parse nor pj_get / pj_get_str (read_members does the lookups, parse_noting the reading); it has no
   __asan_report_* site any more. The 17th target is __asan_stack_malloc_1 (the entry function's own frame, section 6).
     program callees (9)          asan     asan-ubsan
       check_no_overread          0x81904  0x819f0  [1]
       parse_noting               0x81f14  0x81ed0  [1]
       check_bounded_alloc        0x81f8c  0x81f48  [1]
       check_as_written           0x81fb8  0x81f78  [1]
       check_reject_clean         0x82110  0x8208c  [1]
       check_reject_clean_starved 0x82160  0x820e0  [2]
       read_members               0x825f8  0x82554  [1]
       check_round_trip           0x82870  0x82828  [1]
       pj_free                    0x864e4  0x86a24  [1]
     accessors (7)
       fuzz_alloc_ran_out_reset   0x85e08  0x862d4  [1]
       fuzz_alloc_most            0x85e14  0x862e0  [1]
       fuzz_alloc_live            0x85da0  0x8626c  [1]
       fuzz_alloc_count           0x85dcc  0x86298  [2]
       fuzz_alloc_peak_reset      0x85db8  0x86284  [1]
       fuzz_alloc_peak            0x85dac  0x86278  [1]
       fuzz_alloc_ran_out         0x85dfc  0x862c8  [1]
     frame: __asan_stack_malloc_1 0x3dcbc / 0x3dda8 (jal at 0x8173c) and the inline release. *)

(* ---------------------------------------------------------------------- *)
(* 2. Program constants (the same in both images).
      LLVMF_STK  the donor's 32768, kept as an ESTIMATE: the deepest measured paths are the writer arm (LLVMF +
                 check_round_trip + round_trip_text + pj_write + write_value * JSON_DEPTH_MAX 32 + put + fuzz_realloc
                 + interceptor), about 8.6 / 9.1 KiB, and the strtod arm (LLVMF + check_as_written + ex_value * 32 +
                 strtod + __floatscan), about 10.8 / 11.8 KiB (asan / asan-ubsan).
      LIVE_LIB   3 * 2 ^ 32 = 12,884,901,888 (was the donor's 2 ^ 33; decided by the stream's owner), the pre's live bound
                 `blocks_bytes S + LIVE_LIB <= LIVE_MAX`: the harness walk starts its live-room invariant from it
                 (LlvmWalk's Ent102CutsA ec_pre / ec_inv) and pays each callee text's own live premise with it.
                 WITNESS: a Theorem Labs lane's note, the internal file LIVE-BYTES-PEAK.md: the worst
                 call peak is 8,301,643,889 (its section 6, CALL_PEAK at MAXB plus the driver's blocks), and
                 check_round_trip's entry premise is 11,430,643,325 with c-frame-alloc's M4 / M5 (its section 4).
                 SATISFIABLE at the slot's entry: there the live blocks are the driver's, at most 3 (iface_room_at, every
                 earlier call closed: PresetRun call_closed), each < cf_malloc_max = 402,653,184 (chunk_ok_cf), so
                 blocks_bytes S <= 1,207,959,549 and blocks_bytes S + LIVE_LIB <= 14,092,861,437 <= LIVE_MAX = 2 ^ 34 =
                 17,179,869,184 (margin 3,087,007,747).
      LLVMF_FS_CLASS  the fake-stack class of the entry function's own frame: __asan_stack_malloc_1 with size
                 argument 0x80 (jal at entry + 0x70: 0x81650 / 0x8173c on the #102 pins). Section 6 asks that it is in the unit's class set
                 cf_fs_classes; the set itself is never written here.
      SIZE_MAX   the image value of g_fail_at, the disarmed state of the starved checks.
      LCNT       2 ^ 32 (was 2 ^ 24; decided by the stream's owner), a bound on the allocator calls one run of the
                 entry function adds to g_count. An overflow headroom only: it keeps g_count below SIZE_MAX over the 1-4
                 calls (the harness walk's own bound is `e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30`). The walk measured that eight
                 readings of a 3 MiB input make more than 2 ^ 24 allocator calls. *)
Definition LLVMF_STK : Z := 32768. (* PROVISIONAL (harness re-pin) *)
Definition LIVE_LIB : Z := 3 * 2 ^ 32. (* DECIDED: section 2's row *)
Definition LLVMF_FS_CLASS : Z := 1. (* PROVISIONAL (harness re-pin) *)
Definition SIZE_MAX : Z := 2 ^ 64 - 1.
Definition LCNT : Z := 2 ^ 32. (* DECIDED: section 2's row *)

(* ---------------------------------------------------------------------- *)
(* 3. PINV: the cross-call invariant (NEW; it replaces cgif's FINV, lib/Reusable/YD1u.v:67-70).
      cgif's harness opens and closes a file per call, so FINV held the sink's metadata and the stdio cells. Preset's
      harness opens no file; what survives the driver's 1-4 calls is the alloc.c ledger, which between two calls is
      at rest: g_live = 0 (the harness frees every block it took), g_fail_at = SIZE_MAX (every starved check
      re-disarms), g_ran_out = 0 or 1, g_peak anything, g_count = the allocator calls so far. The musl stdio part is
      kept in kind: no thread was started (threaded = need_locks = 0) and no FILE is open (ofl_lock = 0,
      ofl_head = NULL), as the driver's printf / fprintf / fwrite / exit sites need.
      On the #102 pins two more harness cells are at rest between calls: g_most (any value; fuzz_alloc_most sets it
      at every call) and g_own_ran_out (0 or 1; the entry zeroes it at entry + 0x128 and noted() sets it to 1).
      The ledger cells are written by the harness. They are NOT owned statics: the journal's PST parameter exempts
      them (lib/Reusable/YCbqG.v ajournal_x's image clause, PST := the prh_pst, lib/A/PRH_Base.v:752-755, the same
      seven cells), which is how ajournal_cf is instantiated (section 4). The stdio cells are in no PST and no
      owned-static list, so a journalled call leaves them as they are. *)
(* g_ran_out's one byte, in the rd32 / rd64 form (lib/Reusable/YG0n.v:146-147) at width 1. *)
Definition rd8 (rd : reader) (a v : Z) : Prop := forall k, (k < 1)%nat -> rd (a + Z.of_nat k) = Some (le_byte v 1 k).
Definition ledger_rest (rd : reader) (cnt ran : Z) : Prop :=
rd64 rd G_LIVE 0 /\
(exists peak, 0 <= peak < 2 ^ 64 /\ rd64 rd G_PEAK peak) /\
0 <= cnt < 2 ^ 64 /\ rd64 rd G_COUNT cnt /\
rd64 rd G_FAIL_AT SIZE_MAX /\
(ran = 0 \/ ran = 1) /\ rd8 rd G_RAN_OUT ran /\
(* #102: g_most, any value at rest (fuzz_alloc_most sets it at every call) *)
(exists m, 0 <= m < 2 ^ 64 /\ rd64 rd G_MOST m) /\
(* #102: g_own_ran_out, 0 or 1 at rest (the entry zeroes it, noted() sets it to 1) *)
(exists o, (o = 0 \/ o = 1) /\ rd8 rd G_OWN_RAN_OUT o).
Definition pinv_stdio (rd : reader) : Prop :=
rd A_THREADED = Some 0 /\ rd A_NEED_LOCKS = Some 0 /\ rd32 rd A_OFL_LOCK 0 /\ rd64 rd A_OFL_HEAD 0.
Definition PINV (rd : reader) (cnt ran : Z) : Prop := ledger_rest rd cnt ran /\ pinv_stdio rd.

(* The bytes PINV reads, as predicates and as one interval list (the cgif FINV_IVS form). *)
Definition ledger_img (a : Z) : Prop :=
(G_RAN_OUT <= a < G_RAN_OUT + 1) \/ (G_LIVE <= a < G_LIVE + 8) \/ (G_PEAK <= a < G_PEAK + 8) \/
(G_COUNT <= a < G_COUNT + 8) \/ (G_FAIL_AT <= a < G_FAIL_AT + 8) \/ (G_MOST <= a < G_MOST + 8) \/
(G_OWN_RAN_OUT <= a < G_OWN_RAN_OUT + 1).
Definition stdio_img (a : Z) : Prop :=
a = A_THREADED \/ a = A_NEED_LOCKS \/ (A_OFL_LOCK <= a < A_OFL_LOCK + 4) \/ (A_OFL_HEAD <= a < A_OFL_HEAD + 8).
Definition pinv_img (a : Z) : Prop := ledger_img a \/ stdio_img a.
Definition PINV_IVS : list (Z * Z) :=
[(G_RAN_OUT, G_RAN_OUT + 1); (G_LIVE, G_LIVE + 8); (G_PEAK, G_PEAK + 8); (G_COUNT, G_COUNT + 8);
(G_FAIL_AT, G_FAIL_AT + 8); (G_MOST, G_MOST + 8); (G_OWN_RAN_OUT, G_OWN_RAN_OUT + 1);
(A_THREADED, A_THREADED + 1); (A_NEED_LOCKS, A_NEED_LOCKS + 1);
(A_OFL_LOCK, A_OFL_LOCK + 4); (A_OFL_HEAD, A_OFL_HEAD + 8)].

Lemma pinv_img_ivs : forall a, pinv_img a -> exists lo hi, In (lo, hi) PINV_IVS /\ lo <= a < hi.
Proof.
intros a Ha. unfold pinv_img, ledger_img, stdio_img in Ha.
destruct Ha as [[Ha|[Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]]]|[Ha|[Ha|[Ha|Ha]]]];
[ exists G_RAN_OUT, (G_RAN_OUT + 1) | exists G_LIVE, (G_LIVE + 8) | exists G_PEAK, (G_PEAK + 8)
| exists G_COUNT, (G_COUNT + 8) | exists G_FAIL_AT, (G_FAIL_AT + 8) | exists G_MOST, (G_MOST + 8)
| exists G_OWN_RAN_OUT, (G_OWN_RAN_OUT + 1) | exists A_THREADED, (A_THREADED + 1)
| exists A_NEED_LOCKS, (A_NEED_LOCKS + 1) | exists A_OFL_LOCK, (A_OFL_LOCK + 4) | exists A_OFL_HEAD, (A_OFL_HEAD + 8) ];
(split; [unfold PINV_IVS; cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

Definition pinv_ivs_avoid (lo hi : Z) : bool := forallb (fun iv => (hi <=? fst iv) || (snd iv <=? lo))%bool PINV_IVS.
Lemma pinv_ivs_avoid_sound : forall lo hi a, pinv_ivs_avoid lo hi = true -> lo <= a < hi -> ~ pinv_img a.
Proof.
intros lo hi a Hc Ha Hf. destruct (pinv_img_ivs a Hf) as (l & h & Hin & Hlh).
pose proof (proj1 (forallb_forall _ _) Hc (l, h) Hin) as X. cbn [fst snd] in X.
apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.
Lemma pinv_ivs_avoid_sub : forall lo hi lo' hi', pinv_ivs_avoid lo hi = true -> lo <= lo' -> hi' <= hi ->
pinv_ivs_avoid lo' hi' = true.
Proof.
intros lo hi lo' hi' Hc H1 H2. unfold pinv_ivs_avoid in *. apply forallb_forall. intros iv Hiv.
pose proof (proj1 (forallb_forall _ _) Hc iv Hiv) as X. apply orb_prop in X as [X|X]; apply Z.leb_le in X;
apply orb_true_intro; [left | right]; apply Z.leb_le; lia.
Qed.

(* Frame lemmas: PINV depends only on the bytes it reads. *)
Lemma rd64_frame : forall (rd rd' : reader) a v, (forall x, a <= x < a + 8 -> rd' x = rd x) -> rd64 rd a v -> rd64 rd' a v.
Proof. intros rd rd' a v H Hv k Hk. rewrite H by lia. exact (Hv k Hk). Qed.
Lemma rd32_frame : forall (rd rd' : reader) a v, (forall x, a <= x < a + 4 -> rd' x = rd x) -> rd32 rd a v -> rd32 rd' a v.
Proof. intros rd rd' a v H Hv k Hk. rewrite H by lia. exact (Hv k Hk). Qed.
Lemma rd8_frame : forall (rd rd' : reader) a v, (forall x, a <= x < a + 1 -> rd' x = rd x) -> rd8 rd a v -> rd8 rd' a v.
Proof. intros rd rd' a v H Hv k Hk. rewrite H by lia. exact (Hv k Hk). Qed.
Lemma ledger_rest_frame : forall (rd rd' : reader) cnt ran, (forall a, ledger_img a -> rd' a = rd a) ->
ledger_rest rd cnt ran -> ledger_rest rd' cnt ran.
Proof.
intros rd rd' cnt ran H (L & (pk & Pk & P) & C1 & C & F & R1 & R & (m & Mr & M) & (o & O1 & O)). unfold ledger_img in H.
split; [apply (rd64_frame rd); [intros x Hx; apply H; lia | exact L]|].
split; [exists pk; split; [exact Pk | apply (rd64_frame rd); [intros x Hx; apply H; lia | exact P]]|].
split; [exact C1|].
split; [apply (rd64_frame rd); [intros x Hx; apply H; lia | exact C]|].
split; [apply (rd64_frame rd); [intros x Hx; apply H; lia | exact F]|].
split; [exact R1|].
split; [apply (rd8_frame rd); [intros x Hx; apply H; lia | exact R]|].
split; [exists m; split; [exact Mr | apply (rd64_frame rd); [intros x Hx; apply H; lia | exact M]]|].
exists o. split; [exact O1 | apply (rd8_frame rd); [intros x Hx; apply H; lia | exact O]].
Qed.
Lemma pinv_stdio_frame : forall (rd rd' : reader), (forall a, stdio_img a -> rd' a = rd a) ->
pinv_stdio rd -> pinv_stdio rd'.
Proof.
intros rd rd' H (T & N & L & O). unfold stdio_img in H.
split; [rewrite H by lia; exact T|].
split; [rewrite H by lia; exact N|].
split; [apply (rd32_frame rd); [intros x Hx; apply H; lia | exact L]|].
apply (rd64_frame rd); [intros x Hx; apply H; lia | exact O].
Qed.
Lemma pinv_frame : forall (rd rd' : reader) cnt ran, (forall a, pinv_img a -> rd' a = rd a) ->
PINV rd cnt ran -> PINV rd' cnt ran.
Proof.
intros rd rd' cnt ran H (HL & HS). unfold pinv_img in H. split.
- apply (ledger_rest_frame rd); [intros a Ha; apply H; left; exact Ha | exact HL].
- apply (pinv_stdio_frame rd); [intros a Ha; apply H; right; exact Ha | exact HS].
Qed.
(* The same over the memory views the walks carry. *)
Lemma pinv_frame_view : forall (sg : list Segment) (H H' : word -> bool) (mem mem' : word -> option byte) cnt ran,
(forall a, pinv_img a -> mbyte sg (mrestrict H' mem') a = mbyte sg (mrestrict H mem) a) ->
PINV (aview sg H mem) cnt ran -> PINV (aview sg H' mem') cnt ran.
Proof.
intros sg H H' mem mem' cnt ran Hfr. apply pinv_frame. intros a Ha. unfold aview. rewrite (Hfr a Ha). reflexivity.
Qed.
Lemma pinv_stdio_frame_view : forall (sg : list Segment) (H H' : word -> bool) (mem mem' : word -> option byte),
(forall a, stdio_img a -> mbyte sg (mrestrict H' mem') a = mbyte sg (mrestrict H mem) a) ->
pinv_stdio (aview sg H mem) -> pinv_stdio (aview sg H' mem').
Proof.
intros sg H H' mem mem' Hfr. apply pinv_stdio_frame. intros a Ha. unfold aview. rewrite (Hfr a Ha). reflexivity.
Qed.

(* The bridge to the alloc.c ledger (lib/A/PRH_Base.v prh_ledger, which reads the same seven cells through
   val_mem over mrestrict, each at its generated width pi_gz_*, g_ran_out at 1; PINV reads them through rd64 / rd8
   over aview). At an empty harness block list (Lam = []), with g_fail_at disarmed, the two say the same thing, and
   prh_ledger then also forces Hp = []. prh_ledger's two #102 fields, g_most and g_own_ran_out, are not PINV's (see
   prh_ledger_nil_of_pinv). *)
Lemma val_mem_of_aview : forall (sg : list Segment) (H : word -> bool) (mem : word -> option byte) a n v,
(forall k, (k < n)%nat -> aview sg H mem (a + Z.of_nat k) = Some (le_byte v n k)) ->
val_mem sg (mrestrict H mem) a n v.
Proof.
intros sg H mem a n v Hr. unfold val_mem. intros k Hk. specialize (Hr k Hk). unfold aview in Hr.
destruct (mbyte sg (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; rewrite ?E in Hr; cbn in Hr; [|discriminate].
injection Hr as Hb. f_equal. transitivity (Z_to_bv 8 (bv_unsigned b));
[symmetry; apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned | f_equal; exact Hb].
Qed.
Lemma aview_of_val_mem : forall (sg : list Segment) (H : word -> bool) (mem : word -> option byte) a n v,
val_mem sg (mrestrict H mem) a n v ->
forall k, (k < n)%nat -> aview sg H mem (a + Z.of_nat k) = Some (le_byte v n k).
Proof.
intros sg H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn. f_equal.
rewrite stdpp.bitvector.definitions.Z_to_bv_unsigned. unfold bv_wrap, YG0f.le_byte, YO0f.le_byte.
change (bv_modulus 8) with 256. apply Z.mod_mod. lia.
Qed.

Section bridge.
Context {rc : YM05.RunCeil} {L : YP0b.ptable YPsym.asym} {PA : YC4aP.PAImg L}.
(* g_most and g_own_ran_out (prh_ledger's two #102 fields) are PREMISES here, carried as they are (R1 form): PINV
   (ledger_rest) holds them only as SOME value (its two existentials), and prh_ledger names the value. Its consumer, LLVMFuzzerTestOneInput's entry, writes both
   itself before any text reads them (new:808 zeroes g_own_ran_out, new:810 sets g_most = PJ_ALLOC_BOUND (size)), so
   it takes the two premises from its own stores. The image's initialisers are g_most = SIZE_MAX (alloc.c:36) and
   g_own_ran_out = 0 (fuzz_preset.c:76, no initialiser, .bss), but those are the values at program start only:
   from the second call on, g_most is the previous call's PJ_ALLOC_BOUND (size) and g_own_ran_out may be 1 (it is
   zeroed at the entry, new:808, not at the return), so `SIZE_MAX` / `0` under PINV would be false there. *)
Lemma prh_ledger_nil_of_pinv : forall (B : asyms) ly S (W : world (@YC4aP.pa_segs rc L PA)) mem cnt ran most own,
ledger_rest (aview (@YC4aP.pa_segs rc L PA) (w_H W) mem) cnt ran ->
@PRH_Base.prh_most rc preset_prh_img L PA W mem most -> @PRH_Base.prh_own rc preset_prh_img L PA W mem own ->
exists peak, @PRH_Base.prh_ledger rc CfParamsPreset.CfParams_preset preset_prh_img L PA B ly S [] W mem [] peak cnt
  SIZE_MAX ran most own.
Proof.
intros B ly S W mem cnt ran most own (HL & (pk & Pk & HP) & C1 & HC & HF & R1 & HR & _ & _) Hm Ho.
exists pk. unfold PRH_Base.prh_ledger, PRH_Base.prh_glob.
change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.Ledger.lsum []) with 0.
split; [|split; [constructor | split; [constructor | apply Permutation_refl]]].
split; [apply val_mem_of_aview; exact HL|].
split; [apply val_mem_of_aview; exact HP|].
split; [apply val_mem_of_aview; exact HC|].
split; [apply val_mem_of_aview; exact HF|].
split; [apply val_mem_of_aview; exact HR|].
split; [exact Hm|]. split; [exact Ho|].
unfold SIZE_MAX. lia.
Qed.
(* g_most and g_own_ran_out: since the ledger-field sweep (kit walkkit-next 663c569f0c1a) prh_ledger carries the two
   #102 cells as fields (PRH_Base.prh_ledger_most / prh_ledger_own), so ledger_rest's two cell conjuncts follow from
   the ledger itself; no premise. *)
Lemma pinv_ledger_of_prh_ledger_nil : forall (B : asyms) ly S Hp (W : world (@YC4aP.pa_segs rc L PA)) mem peak cnt ran most own,
@PRH_Base.prh_ledger rc CfParamsPreset.CfParams_preset preset_prh_img L PA B ly S Hp W mem [] peak cnt SIZE_MAX ran most own ->
ledger_rest (aview (@YC4aP.pa_segs rc L PA) (w_H W) mem) cnt ran /\ Hp = [].
Proof.
intros B ly S Hp W mem peak cnt ran most own LG.
pose proof (PRH_Base.prh_ledger_live _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HL.
pose proof (PRH_Base.prh_ledger_peak _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HP.
pose proof (PRH_Base.prh_ledger_count _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HC.
pose proof (PRH_Base.prh_ledger_fail _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HF.
pose proof (PRH_Base.prh_ledger_ran _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HR.
pose proof (PRH_Base.prh_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as (Lv & Pk & C1 & F1 & R1).
pose proof (PRH_Base.prh_ledger_heads _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as HPerm.
pose proof (PRH_Base.prh_ledger_most _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as (HMv & HMr).
pose proof (PRH_Base.prh_ledger_own _ _ _ _ _ _ _ _ _ _ _ _ _ LG) as (HOv & HOr).
assert (HM : exists m, 0 <= m < 2 ^ 64 /\ rd64 (aview (@YC4aP.pa_segs rc L PA) (w_H W) mem) G_MOST m)
  by (exists most; split; [exact HMr | exact (aview_of_val_mem _ _ _ _ _ _ HMv)]).
assert (HO : exists o, (o = 0 \/ o = 1) /\ rd8 (aview (@YC4aP.pa_segs rc L PA) (w_H W) mem) G_OWN_RAN_OUT o)
  by (exists own; split; [exact HOr | exact (aview_of_val_mem _ _ _ _ _ _ HOv)]).
change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.Ledger.lsum []) with 0 in HL, Lv.
split.
- split; [exact (aview_of_val_mem _ _ _ _ _ _ HL)|].
  split; [exists peak; split; [lia | exact (aview_of_val_mem _ _ _ _ _ _ HP)]|].
  split; [exact C1|].
  split; [exact (aview_of_val_mem _ _ _ _ _ _ HC)|].
  split; [exact (aview_of_val_mem _ _ _ _ _ _ HF)|].
  split; [exact R1|]. split; [exact (aview_of_val_mem _ _ _ _ _ _ HR)|]. split; [exact HM | exact HO].
- cbn [map] in HPerm. apply Permutation_nil. apply Permutation_sym. exact HPerm.
Qed.
End bridge.

(* The walk reads the run's universe at each call site's own contexts (the walk's Ent102CutsA.ec_univ): the universe closure at
   a larger context list gives it at a smaller one, prh_reach being monotone in its start contexts. *)
Lemma iface_univ_closure_sub {ci : CfImg} : forall (B : asyms) (CTX CTX' : list (list Z)),
  incl CTX' CTX ->
  @PRH_Base.prh_univ_closure preset_prh_img B ci CTX -> @PRH_Base.prh_univ_closure preset_prh_img B ci CTX'.
Proof. intros B CTX CTX' Hi H. exact (@PRH_Base.prh_univ_closure_sub preset_prh_img B ci CTX CTX' Hi H). Qed.

(* LIB_ROOM m holds at EVERY state of the instance and every allowance m <= 2 ^ 36, from its state invariant alone:
   a8's global budget bound (lib/Reusable/YG08cf.v:306 abudget_room_cf). A caller takes WfP_cf from ARcf (inside
   afn_pre_cf) and qloose from qtight (acall_pre_cf carries it), so neither the pre nor the post carries an allowance
   on abudget_cf (header item (12)). *)
Lemma lib_room_of_wf : forall (cp : CfParams) U pp cc bb s m, @WfP_cf cp U pp cc bb s -> qloose s -> cf_hull_ok s -> 0 <= m <= 2 ^ 36 ->
LIB_ROOM abudget_cf m s.
Proof. intros cp U pp cc bb s m W QL HT Hm. unfold LIB_ROOM. exact (abudget_room_cf U pp cc bb s m W QL HT Hm). Qed.

(* ---------------------------------------------------------------------- *)
(* 3b. The run room (NEW; it replaces the margin form ROOM_cf_k S (rk + N_LLVMF), which no state satisfies over the
      driver's 1-4 calls: the lane's note, the internal file n-llvmf.md).
      iface_room_at sm x os H0 hist S states, at the entry of a harness call on the bytes x after the calls whose
      grants are os (P8's model, lib/Spec/PresetRun.v hruns sm x os; sm is the build's strtod model), the premises
      of c-frame-alloc's P8 (lib/Spec/PresetP8.v preset_room) over the instance's room view (h-mani-a8's
      YGcfRoom.room_of_cf):
      (a) the live requests are the model's live requests plus at most 3 of the driver's;
      (b) qtight (YGcfRoom.room_inv_cf), which with Wf_cf gives P8's quar_bytes_ok (YGcfRoom.quar_bytes_ok_cf);
      (c) the instance's free history hist has the quarantine as a suffix (YGcfRoom.quar_fifo_cf), carries
          non-negative requests (YGcfFrees.cf_hist_ok), and its requests are, in order, H0 (the frees before the
          first harness call) followed by the model's frees that ENTER THE QUARANTINE (PresetRunQ.hfrees_q: free_cf
          recycles a chunk above kQuarantineMax at once, Quarantine::Put's size test) (YGcfFrees.cf_frees_follow);
          these give P8's fifo_ok (YGcfFrees.fifo_ok_of_frees_follow).
      The coupling in (c) is the walk's: each free_cf a call makes is the next free of the model run; when the
      quarantine takes the chunk (req_size r <= kQuarantineMax) it is the next element of PresetRunQ.hfrees_q and
      YGcfFrees.cf_frees_step_free carries (c) across it; a larger chunk moves neither hist nor hfrees_q
      (PresetRoomPosKeep.rp_free_parts_big). iface_room_at_entry is P8 at the harness entry.
      (d) A15 (2026-10-30; PART4 row A15, the COUNT meter): PresetRoomPos.rp_count at the whole
          prefix, the same last conjunct as iface_room_pos (lib/Spec/PresetRoomPos.v), so the bridges below carry
          it by position; under the closed secs_steps_cf it bounds the cf layer's secondary map counts nsec_cf S /
          sec_T_cf S by rp_NB / rp_TB plus the model counts nsec / tsec of the calls os. *)
Definition iface_room_at (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
  (H0 : list Z) (hist : list YG00.chunk) (S : astate) : Prop :=
(exists d : list Z, (length d <= 3)%nat /\
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetReqAt.hlive (PresetRun.hruns sm x os) ++ d)) /\
YGcfRoom.room_inv_cf S /\
YGcfRoom.quar_fifo_cf hist S /\ YGcfFrees.cf_hist_ok hist /\
YGcfFrees.cf_frees_follow H0 (PresetRunQ.hfrees_q (PresetRun.hruns sm x os)) hist /\
PresetRoomPos.rp_count (PresetRun.hruns sm x os) S.

Lemma iface_firstn_len_app {A : Type} : forall (l r : list A), firstn (length l) (l ++ r) = l.
Proof. induction l as [|a l IH]; intros r; [reflexivity | cbn; f_equal; apply IH]. Qed.
Lemma iface_nth_len_app {A : Type} : forall (l r : list A) (d : A), nth (length l) (l ++ r) d = nth 0 r d.
Proof. induction l as [|a l IH]; intros r d; [reflexivity | cbn; apply IH]. Qed.
Lemma iface_nth_error_len_app {A : Type} : forall (l r : list A), nth_error (l ++ r) (length l) = nth_error r 0.
Proof. induction l as [|a l IH]; intros r; [reflexivity | cbn; apply IH]. Qed.
Lemma iface_hruns_app : forall sm x a b,
PresetRun.hruns sm x (a ++ b) = PresetRun.hruns sm x a ++ PresetRun.hruns sm x b.
Proof. intros sm x a b. unfold PresetRun.hruns. rewrite List.map_app. apply List.concat_app. Qed.
Lemma iface_hcons_app : forall sm x a b,
PresetRun.hcons sm x (a ++ b) = PresetRun.hcons sm x a ++ PresetRun.hcons sm x b.
Proof. intros sm x a b. unfold PresetRun.hcons. rewrite List.map_app. apply List.concat_app. Qed.
(* a harness call on at most MAXB bytes starts with a consumer allocation (fuzz_copy, check_no_overread) *)
Lemma iface_call_cons_head : forall sm x o1 o2 o0 r, Z.of_nat (length x) <= PresetReqAt.MAXB ->
nth 0 (PresetRun.call_cons sm x o1 o2 o0 ++ r) false = true.
Proof.
intros sm x o1 o2 o0 r Hx. unfold PresetRun.call_cons. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hx).
(* #102 model: three branches (a reading that runs out ends the call), each starting with fuzz_copy's allocation *)
destruct (PresetRun.ranout sm x o1); [reflexivity|]. destruct (PresetRun.ranout sm x o2); reflexivity.
Qed.
Lemma iface_call_evs_head : forall sm x o1 o2 o0 r, Z.of_nat (length x) <= PresetReqAt.MAXB ->
PresetSite17.alloc_at (PresetRun.call_evs sm x o1 o2 o0 ++ r) 0.
Proof.
intros sm x o1 o2 o0 r Hx. unfold PresetSite17.alloc_at, PresetRun.call_evs. cbv zeta.
rewrite (proj2 (Z.ltb_ge _ _) Hx).
destruct (PresetRun.ranout sm x o1); [reflexivity|]. destruct (PresetRun.ranout sm x o2); reflexivity.
Qed.

(* P8's premises at ANY position i of the model run (iface_room_at is the case of a call's entry,
   iface_room_pos_entry), and the walk's fact that one malloc_cf is made at a consumer allocation of the run with
   these premises in its state: run_allocs_follow, a NAMED PREMISE of preset_no_refusal, owner the slot's walk (the
   PROGRAM-WALKS row of LLVMFuzzerTestOneInput). The walk carries iface_room_pos from the entry
   (run_allocs_follow_entry) to each of its malloc_cf calls: a malloc_cf adds its request to the live set, a free_cf
   of a chunk the quarantine takes moves the history by YGcfFrees.cf_frees_step_free (a larger chunk leaves it:
   PresetRoomPosKeep.rp_free_parts_big), and each call must be the next event of hruns.
   iface_room_pos is DEFINED in the leaf lib/Spec/PresetRoomPos.v (the texts carry it; the kit cannot Require this
   file), with this file's former text verbatim except its fifth conjunct, which reads PresetRunQ.hfrees_q, plus a sixth
   and last conjunct, rp_count (PresetRoomPos.v:80-88); re-exported here as the same term. Do not define it again. *)
Notation iface_room_pos := PresetRoomPos.iface_room_pos.
Definition run_allocs_follow (sm : list Z -> Z * Z) (x : list Z) (H0 : list Z) (S : astate) : Prop :=
exists os i hist, iface_room_pos sm x os i H0 hist S /\
  nth i (PresetRun.hcons sm x os) false = true /\ PresetSite17.alloc_at (PresetRun.hruns sm x os) i.

(* THE LIVE-SET BOUNDS at a position of the run (iface_hruns_big, counts_of_room_pos, counts_of_room_pos_rl,
   counts_of_room_pos_ok) live in the plain-free, image-free leaf lib/Spec/PresetRoomCounts.v (moved verbatim, owner's
   decision 19:0xZ); cite them there, qualified. *)
Lemma iface_room_pos_entry : forall sm x os os' H0 hist S, iface_room_at sm x os H0 hist S ->
iface_room_pos sm x (os ++ os') (length (PresetRun.hruns sm x os)) H0 hist S.
Proof.
intros sm x os os' H0 hist S (Hd & T & Q & N & F & C).
unfold iface_room_pos. rewrite iface_hruns_app, iface_firstn_len_app.
exact (conj Hd (conj T (conj Q (conj N (conj F C))))).
Qed.
(* at the entry, the walk's fact holds for the call's first event (check_no_overread's first fuzz_copy) *)
Lemma run_allocs_follow_entry : forall sm x os H0 hist S, iface_room_at sm x os H0 hist S ->
Z.of_nat (length x) <= PresetReqAt.MAXB -> run_allocs_follow sm x H0 S.
Proof.
intros sm x os H0 hist S H Hx. exists (os ++ [(None, None, None)]), (length (PresetRun.hruns sm x os)), hist.
split; [exact (iface_room_pos_entry sm x os _ H0 hist S H)|]. split.
- rewrite iface_hcons_app, <- (PresetRun.hcons_len sm x os), iface_nth_len_app.
  change (PresetRun.hcons sm x [(None, None, None)])
    with (PresetRun.call_cons sm x None None None ++ PresetRun.hcons sm x []).
  exact (iface_call_cons_head sm x None None None _ Hx).
- unfold PresetSite17.alloc_at. rewrite iface_hruns_app, iface_nth_error_len_app.
  change (PresetRun.hruns sm x [(None, None, None)])
    with (PresetRun.call_evs sm x None None None ++ PresetRun.hruns sm x []).
  exact (iface_call_evs_head sm x None None None _ Hx).
Qed.

(* THE ROOM BRIDGE (#102 interface, section 4 of the walk's need): the iface_room_pos at the END of this call's model
   events (index = this call's entry + its events; the entry is iface_room_pos_entry's index) is iface_room_at one
   model call later, at the call's grants (o1, o2, o0) and the history the walk ends with. So the walk's return
   (room_live_cf S' and PresetRoomPos.iface_room_pos at that index) gives preset_lib_post_x's
   `exists o hist', iface_room_at sm x (os ++ [o]) H0 hist' S'` (iface_room_post_of_pos_end). The index is
   PresetCallEntry.call_entry_succ's form (origin/cold/h-hpreset-7-halts-closure); proved here without that file. *)
Lemma iface_room_at_of_pos_end : forall sm x os o1 o2 o0 i H0 hist S,
  iface_room_pos sm x (os ++ [(o1, o2, o0)]) i H0 hist S ->
  i = (length (PresetRun.hruns sm x os) + length (PresetRun.call_evs sm x o1 o2 o0))%nat ->
  iface_room_at sm x (os ++ [(o1, o2, o0)]) H0 hist S.
Proof.
intros sm x os o1 o2 o0 i H0 hist S H Hi.
assert (E0 : PresetRun.hruns sm x [] = []) by reflexivity.
assert (E : PresetRun.hruns sm x (os ++ [(o1, o2, o0)]) = PresetRun.hruns sm x os ++ PresetRun.call_evs sm x o1 o2 o0).
{ rewrite iface_hruns_app, PresetRun.hruns_cons, E0, app_nil_r. reflexivity. }
assert (Hf : firstn i (PresetRun.hruns sm x (os ++ [(o1, o2, o0)])) = PresetRun.hruns sm x (os ++ [(o1, o2, o0)])).
{ rewrite Hi, E, <- List.length_app. apply List.firstn_all. }
unfold PresetRoomPos.iface_room_pos in H. rewrite Hf in H.
destruct H as (Hd & T & Q & N & F & C). exact (conj Hd (conj T (conj Q (conj N (conj F C))))).
Qed.
Lemma iface_room_post_of_pos_end : forall sm x os o1 o2 o0 i H0 hist S,
  iface_room_pos sm x (os ++ [(o1, o2, o0)]) i H0 hist S ->
  i = (length (PresetRun.hruns sm x os) + length (PresetRun.call_evs sm x o1 o2 o0))%nat ->
  exists o hist', iface_room_at sm x (os ++ [o]) H0 hist' S.
Proof.
intros sm x os o1 o2 o0 i H0 hist S H Hi. exists (o1, o2, o0), hist.
exact (iface_room_at_of_pos_end sm x os o1 o2 o0 i H0 hist S H Hi).
Qed.

Section rm. Context {ci : CfImg} {cp : CfParams}.
(* P8 at the harness entry: every primary class has a free slot (PresetP8.preset_room at the call's first event, a
   consumer allocation; the later grants do not matter, so they are taken all granted). *)
Lemma iface_room_at_entry : forall U sm x os H0 hist S c, Wf_cf U S -> iface_room_at sm x os H0 hist S ->
Z.of_nat (length x) <= PresetReqAt.MAXB -> 1 <= c <= 30 -> PresetRoom.room_at (YGcfRoom.room_of_cf S) c.
Proof.
intros U sm x os H0 hist S c W (Hd & T & Q & N & F & _) Hx Hc.
assert (HL : PresetRun.hruns sm x (os ++ [(None, None, None)]) =
  PresetRun.hruns sm x os ++ (PresetRun.call_evs sm x None None None ++ PresetRun.hruns sm x [])).
{ rewrite iface_hruns_app. reflexivity. }
assert (HC : PresetRun.hcons sm x (os ++ [(None, None, None)]) =
  PresetRun.hcons sm x os ++ (PresetRun.call_cons sm x None None None ++ PresetRun.hcons sm x [])).
{ rewrite iface_hcons_app. reflexivity. }
assert (E : firstn (length (PresetRun.hruns sm x os)) (PresetRun.hruns sm x (os ++ [(None, None, None)])) =
  PresetRun.hruns sm x os).
{ rewrite HL. apply iface_firstn_len_app. }
apply (PresetP8.preset_room sm x (os ++ [(None, None, None)]) (length (PresetRun.hruns sm x os))
  (YGcfRoom.room_of_cf S) H0 c Hx).
- rewrite HC, <- (PresetRun.hcons_len sm x os), iface_nth_len_app.
  exact (iface_call_cons_head sm x None None None _ Hx).
- unfold PresetSite17.alloc_at. rewrite HL, iface_nth_error_len_app.
  exact (iface_call_evs_head sm x None None None _ Hx).
- exact Hc.
- rewrite E. exact Hd.
- exact (YGcfRoom.quar_bytes_ok_cf U S W T).
- rewrite E. exact (YGcfFrees.fifo_ok_of_frees_follow hist S H0 _ Q N F).
Qed.

(* NO REFUSAL of the primary allocator, ONCE for the slot (P8's no_null_preset over the instance's NULL fact
   YGcfRoom.malloc_cf_null_full): a malloc_cf of a primary request made at a consumer allocation of the run
   (run_allocs_follow) returns NULL only when the environment's last answer was a refusal (grant flag false).
   No text states the primary room; each keeps its refusal arm, and its walk closes that arm with this lemma. *)
Lemma preset_no_refusal : forall U sm x H0 S n tr ns, Wf_cf U S -> Z.of_nat (length x) <= PresetReqAt.MAXB ->
run_allocs_follow sm x H0 S -> from_primary n = true ->
YGcfRoom.rpost ns (YG00cf.malloc_cf n tr S) (fun g r => fst r = PNull -> g = false).
Proof.
intros U sm x H0 S n tr ns W Hx (os & i & hist & (Hd & T & Q & N & F & _) & Hc & Ha) Hp.
pose proof (YGcfRoom.malloc_cf_null_full U S n tr ns W T) as R. revert R. apply YGcfRoom.rpost_mono.
intros g r Hnf Hnull.
exact (PresetP8.no_null_preset sm x os i (YGcfRoom.room_of_cf S) H0 n (chunk_class n) g (fst r = PNull) Hx Hc Ha
  (YGcfRoom.cls_primary n Hp) Hd (YGcfRoom.quar_bytes_ok_cf U S W T)
  (YGcfFrees.fifo_ok_of_frees_follow hist S H0 _ Q N F) Hnf Hnull).
Qed.

(* The NON-primary room's laws, PROVISIONAL, owner h-mani-a8: they follow from its state-restored form room_live_cf
   (lib/Reusable/YGcfRoomLive.v:1206), with the driver's live set of at most 3 blocks. One text for every
   lane (shape fixed by the parent 04:53Z): the start state, one driver malloc_cf / free_cf step, and the room of
   the driver's two frees after the last call (a8's per-free charge, YGcfRoomFree.v). *)
Definition iface_room_np_init (NP : astate -> Prop) : Prop := NP YG00.init_state.
Definition iface_room_np_step (NP : astate -> Prop) : Prop :=
(forall U S n tr trc p S', Wf_cf U S -> YG01.qtight S -> NP S -> (length (YG01.blocks S) <= 3)%nat ->
  YG00.apath (YG00cf.malloc_cf n tr S) trc (p, S') -> NP S') /\
(forall U S p tr trc S', Wf_cf U S -> YG01.qtight S -> NP S -> (length (YG01.blocks S) <= 3)%nat ->
  YG00.apath (YG00cf.free_cf p tr S) trc (tt, S') -> NP S').
Definition iface_room_np_tail (NP : astate -> Prop) : Prop := forall S, NP S -> ROOM_cf_k S 2.
End rm.

(* ---------------------------------------------------------------------- *)
(* 4. The callee schema (NEW; the donor wrote one bespoke statement per cgif function, e.g. lib/A/ACei.v:73-111).
      One record per callee: its stack need, its allocation-trace contexts, the frame-area blocks it may find held,
      its live-state credit need, its footprint, and its own pre and post. The post is apost_base_cf's Q, whose
      THIRD argument is the post Hp: a callee that returns blocks (pj_parse's tree) returns their hidden heads with
      them. *)
Record fn_iface := MkFn {
  fi_stk : Z;
  fi_ctx : list (list Z);
  fi_frames : Z;
  fi_budget : bvmap 5 word -> Z;
  fi_fp : bvmap 5 word -> (word -> option byte) -> alayout -> astate -> list (Z * Z);
  fi_pre : alayout -> astate -> list Z -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop;
  fi_post : bvmap 5 word -> alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model ->
            alayout -> astate -> list Z -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop
}.

Section v.
(* Instances are passed explicitly: @LIBK LS, CfParams_preset (lib/A/CfParamsPreset.v, a Definition, not an
   Instance), @YC4aP.pa_relro_lo rc L PA. This tree loads #[global] instances of other builds (lib/ZTraceSpec.v
   checksum_shape, and lib/Reusable/YI5b.v src0_sink_head before the Remove Hints above) that an inferred argument could silently pick. *)
Context {rc : YM05.RunCeil} {LS : lib_shape} {L : YP0b.ptable YPsym.asym} {PA : YC4aP.PAImg L}.
(* the instance's code image (YGcfNames.v CfImg): the kit's universe closure (a conjunct of the pre) reads as_universe and
   the allocator code addresses through it *)
Context {ci : CfImg}.
(* The image's listing class (a Theorem Labs lane's lib/Reusable/YC4aP.v PAImg, the kit's form): this file reads its pa_segs, its
   pa_sigma (section 4) and its relro range pa_relro_lo / pa_relro_hi, the last in the read-only predicate PRH_Base.arodata_okP (the same bytes as cgif's
   arodata_okS). *)
(* The second instance's vocabulary, h-mani-a8's. CITED, all constants: CF_MAX and LIB_ROOM
   (lib/Reusable/YGcfNames.v), abudget_cf and ARcf (lib/Reusable/YG0ncf.v), astack_malloc_realizes_cf and
   astack_free_law_cf (lib/Reusable/YG0dcf.v), CfParams_preset. The frame names afn_pre_cf / ajournal_cf /
   apost_base_cf / ablocks_cf are abbreviations (the start of section a) and YCbqG.fregs_kept_x is cited. *)
(* sm: P8's model parameter, the build's strtod model (lib/Prog/ReaderRes.v jr_strtod; the same text in every
   build, lib/Spec/PresetReqAt.v:7); the harness walk instantiates it. *)
Variable sm : list Z -> Z * Z.
(* PROVISIONAL: the NON-primary room of the instance (secondary count, error buffer, batch-class map: what a8's
   ROOM_cf_k measures, lib/Reusable/YGcfRoomKeep.v:26-28), in a form that holds at every call boundary. Owner
   a Theorem Labs lane (room_live_cf, lib/Reusable/YGcfRoomLive.v:1206); its laws are iface_room_np_init /
   iface_room_np_step / iface_room_np_tail (section 3b). *)
Variable iface_room_np : astate -> Prop.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
(* PAYLOAD_ROOM (NEW, this port's): the room the agreement's plain no-refusal premise
   `~ run_scfg_budget_refused Env.alloc_forced_only Images.plain Budgets.Asan.lim_source en_p inp` yields for THIS
   call's payload; the driver walk carries it from TFIB_T to here. Expected to be instantiated `fun _ => True`
   once the harness's NULL sites are fixed, since then no harness path needs an allocation to succeed. *)
Variable PAYLOAD_ROOM : list byte -> Prop.
Local Notation segs := tfibsegs.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* The entry function and its sixteen callees by the listing class's generated names (section 1): pa_sigma of PA,
   which at PA := PI_prog_A / PI_prog_B is h-verbs-1's re-emitted table (lemmas A_entry_<name> / B_entry_<name>). *)
Definition A_LLVMF : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_LLVMFuzzerTestOneInput.
Definition A_check_no_overread : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_check_no_overread.
Definition A_parse_noting : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_parse_noting.
Definition A_check_bounded_alloc : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_check_bounded_alloc.
Definition A_check_as_written : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_check_as_written.
Definition A_check_reject_clean : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_check_reject_clean.
Definition A_check_reject_clean_starved : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_check_reject_clean_starved.
Definition A_read_members : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_read_members.
Definition A_check_round_trip : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_check_round_trip.
Definition A_pj_free : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_pj_free.
Definition A_fuzz_alloc_ran_out_reset : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_fuzz_alloc_ran_out_reset.
Definition A_fuzz_alloc_most : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_fuzz_alloc_most.
Definition A_fuzz_alloc_live : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_fuzz_alloc_live.
Definition A_fuzz_alloc_count : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_fuzz_alloc_count.
Definition A_fuzz_alloc_peak_reset : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_fuzz_alloc_peak_reset.
Definition A_fuzz_alloc_peak : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_fuzz_alloc_peak.
Definition A_fuzz_alloc_ran_out : Z := @YC4aP.pa_sigma rc L PA YPsym.AS_fuzz_alloc_ran_out.
(* THE RUN'S UNIVERSE AND THE CALLEES' CONTEXT (D1): prh_reach has ONE base case, the TOP's own entry context
   (PRH_Base prh_reach_top), and derives every callee's context along the generated call table (prh_reach_call). So
   the slot's context set is this function's own entry context, [[RA_LLVMF]] - not a list of callee return sites
   (that list is not reachable in prh_reach; LlvmWalk's Ent102CutsA.v ec_ctx0, L4Lane's G6). The callee texts below
   and the pre's universe conjunct both take it. *)
Definition iface_ctx0 : list (list Z) := [[RA_LLVMF]].
Section a.
Context {fx : YK11.FPState}.

(* The frame names: abbreviations of YCbqG's journal layer at the instance (a Theorem Labs lane's plan), ARx := ARcf sg B at
   CfParams_preset, PST := the prh_pst, and this image's sink head passed explicitly (no FP in this file opens
   the sink, so its value changes no meaning). *)
Definition ablocks_cf (sg : list Segment) (B : asyms) (ly : alayout) (S : astate) : list (Z * Z) := ablocks B ly S.
Definition afn_pre_cf (sg : list Segment) (B : asyms) (STK : Z) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world sg) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) : Prop :=
YCbqG.afn_pre_x sg B (ARcf (cp := CfParamsPreset.CfParams_preset) sg B) STK ly S Hp W regs mem md ch.
(* the journal at a wild budget WS (YCbqG.ajournal_xw; ajournal_cf is it at WS = []) *)
Definition ajournal_cfw (sg : list Segment) (B : asyms) (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (Hp : list Z) (W : world sg) (mem : word -> option byte) (md : Model)
  (own : list (Z * Z)) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world sg) (mem' : word -> option byte)
  (md' : Model) (k : Z) (WS : list (list Z)) : Prop :=
YCbqG.ajournal_xw (SK := preset_sink_head) sg B (@PRH_Base.prh_pst preset_prh_img)
  (ARcf (cp := CfParamsPreset.CfParams_preset) sg B) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
(* the same journal over a world relation R (YCbqG.ajournal_xwR, R after the instance arguments as there; header
   item (14)): ajournal_cfw is it at wle (ajournal_cfw_R_wle) *)
Definition ajournal_cfwR (sg : list Segment) (B : asyms) (R : world sg -> world sg -> Prop) (STK sp0 : Z)
  (FP : list (Z * Z)) (ly : alayout) (S : astate) (Hp : list Z) (W : world sg) (mem : word -> option byte) (md : Model)
  (own : list (Z * Z)) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world sg) (mem' : word -> option byte)
  (md' : Model) (k : Z) (WS : list (list Z)) : Prop :=
YCbqG.ajournal_xwR (SK := preset_sink_head) sg B (@PRH_Base.prh_pst preset_prh_img)
  (ARcf (cp := CfParamsPreset.CfParams_preset) sg B) R STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
Lemma ajournal_cfw_R_wle : forall sg B STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS,
  ajournal_cfw sg B STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS =
  ajournal_cfwR sg B (@wle sg) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k WS.
Proof. reflexivity. Qed.
Definition ajournal_cf (sg : list Segment) (B : asyms) (STK sp0 : Z) (FP : list (Z * Z))
  (ly : alayout) (S : astate) (Hp : list Z) (W : world sg) (mem : word -> option byte) (md : Model)
  (own : list (Z * Z)) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world sg) (mem' : word -> option byte)
  (md' : Model) (k : Z) : Prop :=
YCbqG.ajournal_x (SK := preset_sink_head) sg B (@PRH_Base.prh_pst preset_prh_img)
  (ARcf (cp := CfParamsPreset.CfParams_preset) sg B) STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k.
Definition apost_base_cf (sg : list Segment) (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world sg) (mem : word -> option byte) (md : Model)
  (Q : alayout -> astate -> list Z -> world sg -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world sg -> config -> Prop :=
YCbqG.apost_base_x (SK := preset_sink_head) sg B (@PRH_Base.prh_pst preset_prh_img)
  (ARcf (cp := CfParamsPreset.CfParams_preset) sg B) STK FP regs ly S Hp W mem md Q.
(* the float form (header item (9)): YCbqG.apost_base_xF at the same arguments *)
Definition apost_base_cfF (sg : list Segment) (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world sg) (mem : word -> option byte) (md : Model)
  (Q : alayout -> astate -> list Z -> world sg -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  : world sg -> config -> Prop :=
YCbqG.apost_base_xF (SK := preset_sink_head) sg B (@PRH_Base.prh_pst preset_prh_img)
  (ARcf (cp := CfParamsPreset.CfParams_preset) sg B) STK FP regs ly S Hp W mem md Q.

(* ---------------------------------------------------------------------- *)
(* 5. The interface. Donor: YCfn.v:31-67 / A/ACfn.v:33-69. *)
Definition preset_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
(W : world segs) (mem : word -> option byte) (md : Model)
(p n : Z) (pl : list byte) (cnt ran : Z) (os : list (option nat * option nat * option nat)) (H0 : list Z)
(hist : list YG00.chunk) : Prop :=
afn_pre_cf segs B LLVMF_STK ly S Hp W regs mem md [] /\
(* NAMED PREMISE: the empty frame chain above is achain's first disjunct, taken under s0 < YM05.alloc_ceiling
   (achain_low): target_run holds the payload length in s0 at this call (header item (7)) *)
s0Z regs < YM05.alloc_ceiling /\
(* the entry rounding mode is round-to-nearest (frm = 0) *)
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
YK0o.frm_zero (@YK11.fp_csr fx) /\
raZ regs = RA_LLVMF /\
getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks_cf segs B ly S))) /\
n = Z.of_nat (length pl) /\ garr8 segs (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
frames S = [] /\
(* the run room (section 3b): the non-primary room, P8's premises at this entry, and THE HULL CLOSED SET: the
   earlier calls' grant list os has at most 3 entries (target_run makes at most 4 harness calls, so a call's
   position inside it has at most 4), which the hull budget at a run position reads; one conjunct, so the
   projections of the conjuncts after it stay *)
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
(iface_room_np S /\ iface_room_at sm (map (fun b : byte => bv_unsigned b) pl) os H0 hist S /\ (length os <= 3)%nat) /\
(* THE WILD ROOM (clause 4b of the kit's batch; lib/Reusable/YCbqGwild.v section 2, wild_room and wild_room_admits):
   the entry depot's wild traces plus YCbqGwild.K_LLVMF
   more fit in the instance universe's u_wmax, so the call's wild allocator sites stay admitted (the slot post's
   journal is at a budget of at most YCbqGwild.K_LLVMF fresh wild traces) *)
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
YCbqGwild.wild_room (as_universe B) [] YCbqGwild.K_LLVMF (st_depot S) /\
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
PRH_Base.arodata_okP segs (@YC4aP.pa_relro_lo rc L PA) (@YC4aP.pa_relro_hi rc L PA) B (aview segs (w_H W) mem) /\
(* no hidden head is outstanding between calls: alloc.c unhides every block before it frees it *)
Hp = [] /\
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
PINV (aview segs (w_H W) mem) cnt ran /\ cnt + LCNT <= SIZE_MAX /\
(* D2 (owner 17:34Z): the count headroom the check texts take (PRH_FnCheck tcheck_no_overread_specX /
   tcheck_reject_clean_starved_specX); the DRIVER proves it at the slot call - it is never a premise of the top *)
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
cnt + LCNT < 2 ^ 62 - 2 ^ 30 /\
PAYLOAD_ROOM pl /\
Fs.fs_sorted (m_fs md) = true /\
mo_ok MT S (XM_LIB n) /\
(* the errbuf slot is placed like a live secondary (a8's xs_placed_cf, lib/Reusable/YG0ncf.v, kept by YGcfXs.v) *)
xs_placed_cf ly S /\
(* header item (8): the call configuration's FULL overlay is in memnorm form (the callee texts' entry premise, same term) *)
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
YAkMemnorm.memnorm segs mem /\
(* header item (11): the instance universe's closure at this body's allocator-reaching contexts (no DW) *)
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
@PRH_Base.prh_univ_closure preset_prh_img B ci iface_ctx0 /\
(* THE LIVE REAL STACK ABOVE sp, AT THE SLOT CALL (a Theorem Labs lane's chain ruling, 2026-10-30 09:23Z: the unguarded
   conjunct, appended last, on every text of the caller chain of round_trip_text up to the harness entry; the first
   link is a Theorem Labs lane's ruling 2026-10-30 10:58Z on PRH_FnCheck.tround_trip_text_specX). The callee text
   PRH_FnCheck.tcheck_round_trip_specX (pcc_check_round_trip) takes `YGcallStackUp.astack_up_x segs ly W (spZ regs)
   mem` as its last premise at its call state (fuzz_preset.c new:832), and nothing else gives it there: afn_pre_cf
   gives only this function's window [sp - LLVMF_STK, sp), and no AR_laws_x field reads a real-stack byte
   (YGcallStackUp.v's header). MET AT THE REAL CALL STATE of round_trip_text given check_round_trip's entry fact:
   the check_round_trip walks, YGcallStackUp.astack_up_at_xwR at Crt102Arms.v:1102-1109 and Crt102B_RRT.v:1096-1101 (first by a witness at commit 5208cc4f6eb0, rtt_up_at_call_A /
   rtt_up_at_call_B; rc=0, Print Assumptions primitives only; control C2 without the entry fact FAILS on both
   images). NOT GUARDED (PRH_FnEx.tsame_specX's guarded twin is a different statement). Its root at main's
   entry is lib/AU/PresetD1pBPfC.v:62 H_stackup_main_B_holds (Qed, by StackUpMainB.stack_up_main_W1_B). *)
(* SUPPLIED BY THE DRIVER (main / target_run slot call); the callee texts take it as a premise. *)
YGcallStackUp.astack_up_x segs ly W (spZ regs) mem.
(* Dropped from the donor's pre: asink_none, the free fd, ameta_inv and its parameter M. *)

(* The payload buffer plus 8 bytes lies below the allocator ceiling (the harness walk's S3 reads it). It follows from
   the pre alone: a non-empty payload is a live block of the instance (ablocks_cf), and the instance's chunk geometry
   (YG0scf.chunk_facts_cf, from ARcf inside afn_pre_cf) puts its user end at least 8 bytes below YM05.alloc_ceiling. A
   primary chunk ends inside its class region, at most kFreeArrayOffset (3.5 GiB) past the region base, and the
   region's 2 ^ 32 bytes end at or below YM05.alloc_ceiling (YG0s.region_in_prim). A secondary chunk's mapping ends at or
   below YM05.alloc_ceiling, and past the user end there are at least rz_size n >= 16 bytes of right redzone before the
   mapping ends (YG0a.secondary_geometry: kPage + rounded_size n + 2 rz_size n <= sec_map_size n). *)
Lemma preset_lib_pre_pay8 : forall regs ly S Hp (W : world segs) mem md p n pl cnt ran os H0 hist,
preset_lib_pre_x regs ly S Hp W mem md p n pl cnt ran os H0 hist -> 0 < n -> p + n + 8 <= YM05.alloc_ceiling.
Proof.
intros regs ly S Hp W mem md p n pl cnt ran os H0 hist Hpre Hn.
destruct Hpre as (HA & _ & _ & _ & _ & _ & HB & _).
destruct HB as [[Hn0 _] | (_ & Hin)]; [lia|].
unfold afn_pre_cf, YCbqG.afn_pre_x, ARcf in HA. destruct HA as ((M & _) & _).
unfold ablocks_cf in Hin. apply YG0s.In_ablocks in Hin as (k & Hk & _ & Hu & Hr). subst p n.
pose proof (YG0scf.chunk_facts_cf B ly S Hp _ k M Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
rewrite G4. unfold YG0f.ASAN_CEIL in G2.
assert (RQ : req_size (ck_req k) = ck_req k) by (unfold req_size; destruct (Z.eqb_spec (ck_req k) 0); lia).
rewrite RQ in G8.
destruct (ck_beg k) as [|off|r o|c q] eqn:Eb; try solve [destruct GG].
- cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & _ & Gxs & Gal).
  pose proof (YG0s.region_in_prim ly (prim_class off) (amc_layout _ _ _ _ _ M) ltac:(lia)) as (_ & _ & _ & _ & R5).
  unfold YG0f.ASAN_CEIL in R5. unfold kFreeArrayOffset in Gal. lia.
- destruct GG as (_ & Hfp & Gbase & Gext & _).
  pose proof (secondary_geometry (ck_req k) ltac:(lia) Hfp) as (_ & S2 & _ & [S4 _] & _).
  pose proof (rounded_size_bounds (ck_req k) ltac:(lia)) as [[RS _] _].
  unfold needed_primary in S2. unfold ck_rz in *. unfold kPage in *. lia.
Qed.

Definition preset_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
(W : world segs) (mem : word -> option byte) (md : Model)
(p n cnt : Z) (pl : list byte) (os : list (option nat * option nat * option nat)) (H0 : list Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
(* the empty footprint in place of the donor's [sink_token]; the post Hp is [] again. k stays cgif's relative
   per-segment event count; the donor's `k <= EV_LIB` is dropped with the event cap. *)
(* the journal at a WILD BUDGET (clause 4b of the kit's batch): at most YCbqGwild.K_LLVMF fresh wild traces beyond the entry's *)
(exists WS, YCbqGwild.wbudget [] YCbqGwild.K_LLVMF WS /\
   ajournal_cfw segs B LLVMF_STK (spZ regs) [] ly S Hp W mem md [] ly' S' [] W' mem' md' k WS) /\
(* the run room again, one model call later: the call's grants o and the instance's free history hist' *)
(iface_room_np S' /\ exists o hist', iface_room_at sm (map (fun b : byte => bv_unsigned b) pl) (os ++ [o]) H0 hist' S') /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks_cf segs B ly' S') (ablocks_cf segs B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
(exists cnt' ran', PINV (aview segs (w_H W') mem') cnt' ran' /\ cnt <= cnt' <= cnt + LCNT) /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
(* the errbuf slot is still placed: the driver loop carries xs_placed_cf across calls (last conjunct but one) *)
xs_placed_cf ly' S' /\
(* header item (8): memnorm KEPT, on the return configuration's FULL overlay (the caller chains it to its next call) *)
YAkMemnorm.memnorm segs mem'.
(* Dropped from the donor's post: asink_none, ameta_inv. *)

(* THE SLOT OVER A WORLD RELATION R (header item (14)): preset_lib_post_xR and preset_lib_contract_xR below are COPIES
   of preset_lib_post_x and preset_lib_contract_x, the journal at ajournal_cfwR R and the continuation's world step
   `R W W'`; the plain bodies stay, and preset_lib_post_x_R_wle / preset_lib_contract_x_R_wle (by reflexivity) check
   that each plain form IS its R form at wle. *)
Definition preset_lib_post_xR (R : world segs -> world segs -> Prop) (regs : bvmap 5 word) (ly : alayout) (S : astate)
(Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model)
(p n cnt : Z) (pl : list byte) (os : list (option nat * option nat * option nat)) (H0 : list Z) (l : lleaf)
(ly' : alayout) (S' : astate) (W' : world segs) (regs' : bvmap 5 word)
(mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
(exists WS, YCbqGwild.wbudget [] YCbqGwild.K_LLVMF WS /\
   ajournal_cfwR segs B R LLVMF_STK (spZ regs) [] ly S Hp W mem md [] ly' S' [] W' mem' md' k WS) /\
(iface_room_np S' /\ exists o hist', iface_room_at sm (map (fun b : byte => bv_unsigned b) pl) (os ++ [o]) H0 hist' S') /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
Permutation (ablocks_cf segs B ly' S') (ablocks_cf segs B ly S) /\
(forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
(exists cnt' ran', PINV (aview segs (w_H W') mem') cnt' ran' /\ cnt <= cnt' <= cnt + LCNT) /\
mo_le MT S S' (XN_LIB n) /\
(forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
xs_placed_cf ly' S' /\
YAkMemnorm.memnorm segs mem'.
Lemma preset_lib_post_x_R_wle : forall regs ly S Hp W mem md p n cnt pl os H0 l ly' S' W' regs' mem' md' k,
  preset_lib_post_x regs ly S Hp W mem md p n cnt pl os H0 l ly' S' W' regs' mem' md' k =
  preset_lib_post_xR (@wle segs) regs ly S Hp W mem md p n cnt pl os H0 l ly' S' W' regs' mem' md' k.
Proof. reflexivity. Qed.

Definition preset_lib_contract_x : Prop :=
forall ly S Hp (W : world segs) (regs : bvmap 5 word) mem md p n pl cnt ran os H0 hist (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
preset_lib_pre_x regs ly S Hp W mem md p n pl cnt ran os H0 hist ->
(forall (l : lleaf) (W' : world segs) (c' : config),
wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(* the return config at a float state fx' (YCbqG.apost_base_xF's form): rounding mode 0 and the callee-saved f
   registers kept (YCbqG.fregs_kept_x) *)
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
YK0o.frm_zero (@YK11.fp_csr fx') /\ YCbqG.fregs_kept_x fx fx' /\
preset_lib_post_x regs ly S Hp W mem md p n cnt pl os H0 l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (@LIBK LS pl (m_fs md) K).

Definition preset_lib_contract_xR (R : world segs -> world segs -> Prop) : Prop :=
forall ly S Hp (W : world segs) (regs : bvmap 5 word) mem md p n pl cnt ran os H0 hist (K : lleaf -> TSet),
AI segs (w_H W) (w_A W) md ->
preset_lib_pre_x regs ly S Hp W mem md p n pl cnt ran os H0 hist ->
(forall (l : lleaf) (W' : world segs) (c' : config),
R W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
(exists (fx' : YK11.FPState) ly' S' regs' mem' md' k,
c' = mkCfg (@YK11.mkst fx' regs' (w64 RA_LLVMF) mem' (YK11.seg_rom segs)) md' /\
YK0o.frm_zero (@YK11.fp_csr fx') /\ YCbqG.fregs_kept_x fx fx' /\
preset_lib_post_xR R regs ly S Hp W mem md p n cnt pl os H0 l ly' S' W' regs' mem' md' k) ->
srealizes segs c' (K l)) ->
srealizes segs (cfg_at segs A_LLVMF regs mem md) (@LIBK LS pl (m_fs md) K).
Lemma preset_lib_contract_x_R_wle : preset_lib_contract_x = preset_lib_contract_xR (@wle segs).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 6. The callee contracts: one per callee of LLVMFuzzerTestOneInput (section 1's list) and the entry function's
      own fake-stack frame. Donor: YD2o.v:28-34 takes wfn and one hypothesis per cgif library function; preset takes
      no wfn. The record is what the closure (PresetCfiB) supplies and the harness walk (Ent102SeamB's preset_lib_x_stmt_B_holds) consumes. *)
Definition afn_spec_cf (pc : Z) (F : fn_iface) : Prop :=
forall ly S Hp (W : world segs) (regs : bvmap 5 word) mem md ch,
afn_pre_cf segs B (fi_stk F) ly S Hp W regs mem md ch ->
In (raZ regs :: spine ch) (fi_ctx F) ->
Z.of_nat (length (frames S)) <= fi_frames F ->
PRH_Base.arodata_okP segs (@YC4aP.pa_relro_lo rc L PA) (@YC4aP.pa_relro_hi rc L PA) B (aview segs (w_H W) mem) ->
LIB_ROOM (abudget_cf (cp := CfParamsPreset.CfParams_preset)) (fi_budget F regs) S ->
fi_pre F ly S Hp W regs mem md ->
(* header item (9): the entry rounding mode is 0, and the post is the float form *)
YK0o.frm_zero (@YK11.fp_csr fx) ->
SRr segs W (cfg_at segs pc regs mem md)
(apost_base_cfF segs B (fi_stk F) (fi_fp F regs mem ly S) regs ly S Hp W mem md (fi_post F regs ly S Hp W mem md)).

(* THE MEMNORM-KEEPING FRAME CALL (the internal file llvm-iface-need.md section 5): the engine's YGcallMxmn.astack_malloc_realizes_xm
   (origin/cold/c-omx-alloc-preset-s1b 459129c18903, blob 2b01e06e3fc4: FCiface's astack_malloc_realizes_x with the
   keep (memnorm segs mem -> memnorm segs mem') as the last post conjunct) at ARx := ARcf, so not a second copy. By
   conversion it is LlvmWalk's Ent102CutsA.ec_stack_malloc_cfm (ecall_pre_cf is ecall_pre_x at ARcf, FCapiCf.v's
   header). The interface's post keeps memnorm, and the cf form constrains mem' only through aview, so without the
   keep the post is not payable after the frame call.
   THE SUPPLIER is per image and per class: h-hpreset-7's frame-class lane (origin/cold/h-hpreset-7-frameclass
   d05d97a36005) proves stack_malloc0_contract_xm for cid 0 and stack_malloc1_contract_xm for cid 1, in
   lib/A/FCm01xm.v (:24, :32) and its twin lib/AU/FCm01xm.v (:25, :33), at ARx := ARcf through h-mani-a8's
   FCifaceCf.fs_iface_ARcf. The capacity premise `count_cid cid (frames S) < fs_frames cid` is NOT in the contract:
   every caller discharges it at its own entry state (YGcallSx.aj_stack_malloc_at_x, lib/Reusable/YGcallSx.v:158,
   premise :164), because no contract states `a0 <> 0`. On #102 the frame-class walk is expected to carry over by
   relocation (h-rw-pre-4 is confirming it per symbol). *)
Definition astack_malloc_realizes_cfm (sg : list Segment) (B : asyms) (cid : Z) : Prop :=
  YGcallMxmn.astack_malloc_realizes_xm (fx := fx) sg B (ARcf (cp := CfParamsPreset.CfParams_preset) sg B) cid.
(* forgetting the keep gives the cf form (YGcallMxmn.astack_malloc_realizes_xm_forget, by conversion) *)
Lemma astack_malloc_realizes_cfm_cf : forall sg B cid, astack_malloc_realizes_cfm sg B cid ->
  astack_malloc_realizes_cf (fx := fx) (rc := rc) (cp := CfParamsPreset.CfParams_preset) sg B cid.
Proof.
intros sg B0 cid H. apply YGcallMxmn.astack_malloc_realizes_xm_forget. exact H.
Qed.

(* D1 (owner 17:34Z): each callee's contract IS the text for it (lib/A/PRH_Fn*.v t<f>_specX), at every float state
   at the slot's context set iface_ctx0, the instance's frame names (PST := the kit's
   prh_pst, ARx := ARcf /\ xs_placed_cf at CfParams_preset - the walk's Ent102CutsA.ec_ARx - and preset_sink_head),
   the room-live instance prh_room_live_a8, and check_round_trip's two literal addresses A_MOD_AT / A_STAMP. The
   seam (lib/A/Prog/Ent102SeamA.v / lib/AU/Prog/Ent102SeamB.v) discharges all 16 by `exact` from the walk's ec_texts
   fields, which ARE these texts (the walk's granted forms of three of them are derived from the batch kit's texts in
   lib/A/Prog/Ent102OfPost.v). The abstract fn_iface records and
   afn_spec_cf of the donor are gone from the slot. Each text is proved by its own function walk (owners: the walk's
   lib/A/Ent102CutsA.v header and the lane's note, the internal file seam-premises.md). *)
Variables A_MOD_AT A_STAMP : Z.
Definition iface_ARx : alayout -> astate -> list Z -> world (@YC4aP.pa_segs rc L PA) -> (word -> option byte) ->
  Model -> Prop :=
  fun ly S Hp W mem md => ARcf (cp := CfParamsPreset.CfParams_preset) (@YC4aP.pa_segs rc L PA) B ly S Hp W mem md /\
    xs_placed_cf ly S.
Local Notation RLX := (@PRH_Base.prh_room_live_a8 CfParamsPreset.CfParams_preset).
Local Notation CPX := CfParamsPreset.CfParams_preset.
(* The field list follows section 1's callee list on the #102 pins: the nine program callees, then the seven alloc.c
   accessors, in that order. *)
Record preset_callee_contracts : Prop := MkCallees {
  pcc_check_no_overread : forall fy : YK11.FPState,
    @PRH_FnCheck.tcheck_no_overread_specX fy rc ci CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head iface_ctx0;
  pcc_parse_noting : forall fy : YK11.FPState,
    @PRH_FnCheck.tparse_noting_specX fy rc ci CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head iface_ctx0;
  pcc_check_bounded_alloc : forall fy : YK11.FPState,
    @PRH_FnCheck.tcheck_bounded_alloc_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_check_as_written : forall fy : YK11.FPState,
    @PRH_FnCheck.tcheck_as_written_specX fy rc ci CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head iface_ctx0;
  pcc_check_reject_clean : forall fy : YK11.FPState,
    @PRH_FnCheck.tcheck_reject_clean_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_check_reject_clean_starved : forall fy : YK11.FPState,
    @PRH_FnCheck.tcheck_reject_clean_starved_specX fy rc ci CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head
      iface_ctx0;
  pcc_read_members : forall fy : YK11.FPState,
    @PRH_FnCheck.tread_members_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_check_round_trip : forall fy : YK11.FPState,
    @PRH_FnCheck.tcheck_round_trip_specX fy rc ci CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head iface_ctx0
      A_MOD_AT A_STAMP;
  pcc_pj_free : forall fy : YK11.FPState,
    @PRH_FnPj.tpj_free_specX fy rc ci CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head iface_ctx0
      PRH_Base.DOC_D;
  pcc_fuzz_alloc_ran_out_reset : forall fy : YK11.FPState,
    @PRH_FnAlloc.tfuzz_alloc_ran_out_reset_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_fuzz_alloc_most : forall fy : YK11.FPState,
    @PRH_FnCheck.tfuzz_alloc_most_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_fuzz_alloc_live : forall fy : YK11.FPState,
    @PRH_FnAlloc.tfuzz_alloc_live_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_fuzz_alloc_count : forall fy : YK11.FPState,
    @PRH_FnAlloc.tfuzz_alloc_count_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_fuzz_alloc_peak_reset : forall fy : YK11.FPState,
    @PRH_FnAlloc.tfuzz_alloc_peak_reset_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_fuzz_alloc_peak : forall fy : YK11.FPState,
    @PRH_FnAlloc.tfuzz_alloc_peak_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  pcc_fuzz_alloc_ran_out : forall fy : YK11.FPState,
    @PRH_FnAlloc.tfuzz_alloc_ran_out_specX fy rc CPX preset_prh_img RLX L PA B iface_ARx preset_sink_head;
  (* __asan_stack_malloc_1: the entry function's frame, from the unit's frame-area class set (AsanAPI_cf's
     aa_stack_malloc_cf, YGcfNames.v:612; LLVMF_FS_CLASS is in it, llvmf_fs_class_ok below), and its inline
     release *)
  pcc_stack_malloc : forall cid, In cid (@cf_fs_classes CfParamsPreset.CfParams_preset) ->
    astack_malloc_realizes_cfm segs B cid;
  pcc_stack_free : astack_free_law_cf (rc := rc) (cp := CfParamsPreset.CfParams_preset) segs B
}.

End a.

(* The obligation the harness walk (the PROGRAM-WALKS row of LLVMFuzzerTestOneInput) discharges. The callee contracts
   (the texts, D1) hold at EVERY float state (header item (9)): a callee is called at the float state the previous one
   returned in. Arguments: {fx}, then check_round_trip's two literal addresses (the top passes the generated ones).
   The contract is the R form at the re-hiding relation YA0nH.wle' segs RZ_cf (header item (14)). *)
Definition preset_lib_x_stmt {fx : YK11.FPState} (A_MOD_AT A_STAMP : Z) : Prop :=
(forall fx0 : YK11.FPState, @preset_callee_contracts fx0 A_MOD_AT A_STAMP) ->
@preset_lib_contract_xR fx (YA0nH.wle' segs (@YGcfRehidePost.RZ_cf rc)).

(* The program slot as the composition takes it (the donor's tfib_lib_contract_x_all, YCfn.v:69-70), at the
   re-hiding relation YA0nH.wle' segs RZ_cf (header item (14)). *)
Definition preset_lib_contract_x_all : Prop :=
  forall fx : YK11.FPState, @preset_lib_contract_xR fx (YA0nH.wle' segs (@YGcfRehidePost.RZ_cf rc)).
End v.

(* The entry function's frame class is one of preset's frame-area classes. *)
Lemma llvmf_fs_class_ok : In LLVMF_FS_CLASS (@cf_fs_classes CfParamsPreset.CfParams_preset).
Proof. cbn. right. left. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* 7. At ZTraceSpec.checksum_shape (LIBK pl fs K := K (LL 0 fs [])) the library continuation is one leaf, so cgif's
      ff_unl_has_nil and ff_libk_has_nil (the donor's lib/YD1q.v:21-32, lib/A/AD1q.v:25-36) collapse into this
      lemma; cgif's YI0a (its file-system instance and ff_unl / ff_libk) is not needed. *)
Lemma libk_has_nil : forall pl fs (K : lleaf -> TSet), (forall l, K l []) ->
@LIBK OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape pl fs K [].
Proof. intros pl fs K HK. apply HK. Qed.
