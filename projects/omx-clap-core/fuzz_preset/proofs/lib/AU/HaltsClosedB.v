(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/HaltsClosedB.v, with its module paths and module names changed; 443 of its 496 lines of code are new or changed and 120 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: fuzz_preset's asan-ubsan image on the #102 pins (image B', pin d663f82d7f488d30,
   twin c90d4fa54d43160b): the halts top Statements.asan_ubsan_halts, made from the halting theorem of
   proofs/cgif/cgif_file_fuzzer/lib/Halts_tfib.v by way of lib/AU/HaltsTop.v. *)
(* rule 24: no function proved (kind: composition).
   BASE: the kit cut preset-tree-at-2026-10-30T04-57-22Z.tsv (sha256 652fe98064b9; internal record) (the kit's texts lib/A/PRH_*, the no-DW interface
   lib/AU/PresetCfnB.v), with the kit's first post-batch change merged: prh_univ_closure's fifth clause
   (preset-tree-at-2026-10-30T08-55-41Z.tsv (sha256 56822366e9ba; internal record): PRH_Base, PRH_Witness.c5_padded_trace_B, ACej, WildRoomInstA). Another
   version of this file, merged with a later change, cites that change's swapped unpoison row, with
   PresetD1pBPf.v re-fit to that change's YGcfNilInit.v; here the cut's row keeps its stand-in. The
   program slot (sections A-C) is the B' program slot of the version HaltsClosedB.v (sha256 3fcaea9ffeb8; internal record) of this
   path, rebound to the cut's texts; the composition (sections D-F) is the donor's
   (commit 2f1789b29f0, this path, sections C-E) on the B' closed room export
   PresetD2pBPf.TFIB_T_room_all_B_closed_stmt_holds (lib/AU/PresetD2pBPf.v; statement
   lib/AU/PresetDrvTopBStmt.v TFIB_T_room_all_B_closed_stmt), whose program SLOT section C proves.
   THE INSTANCE (the driver's and the seam's, cited, not chosen here):
   - PAYLOAD_ROOM := fun _ => True: the composed B' top lib/AU/Prog/Ent102DrvTopB.v
     and its A' twin lib/A/Prog/Ent102DrvTopA.v:7; the interface's own
     expectation, lib/AU/PresetCfnB.v:724-727. PAYLOAD_ROOM occurs in the slot only in its PRE (PresetCfnB.v:832,
     `PAYLOAD_ROOM pl`), so at True the slot assumes no room; the seam proves the slot for every PAYLOAD_ROOM, so it holds
     at True. In the export's conclusion the room premise is then I. PAYLOAD_ROOM_dec and the no-room arm are LEMMAS
     (PAYLOAD_ROOM_dec_B, payload_refusal_B: left I; the no-room premise ~ True is absurd).
   - sm := ReaderRes.jr_strtod, iface_room_np := np_live_B, A_MOD_AT / A_STAMP := Ent102InstB.ia_mod_at /
     ia_stamp: the B' seam's values (lib/AU/Prog/Ent102SeamB.v:6-9).
   - XM_LIB / XN_LIB: NOT fixed by the driver or the seam (the seam quantifies them; Ent102DrvTopB keeps them as Section
     variables). The top's type does not mention them and ameter_triv reads neither, so they are INSTANTIATED here as
     fun _ => 0 (XLIB0), not left as binders.
   DISCHARGED HERE BY CITATION (each result's file is in this tree; by-path takes and owners in the commit):
   - the harness slot H_preset_lib_x_stmt_B: the B' seam's Ent102SeamB.preset_lib_x_stmt_B_holds (no premise);
   - parse_noting: PN102BTop.tparse_noting_specX_TfibB (lib/B/Prog/PN102BTop.v); its four
     premises: fuzz_alloc_live (BridgeB pcc102), fuzz_alloc_ran_out (FuzzAllocAccInstB102),
     check_reject_clean (below) and the pj_parse text (H_text_pj_parse_B, open);
   - check_as_written: Caw102B_Img.caw_B_top_inst (lib/B/Prog/Caw102B_Img.v); its
     premises: ex_value (ExvB_Inst.ex_value_holds_B_closed, lib/B/Prog/ExvB_Inst.v), ex_ws
     (ex_ws_cf.ex_ws_holds_B, on the cut), fuzz_alloc_ran_out (on the cut), free / malloc (the export's rows, malloc at
     every float state);
   - check_no_overread: Cno102B_TopInst.cnb_B_top_inst (lib/B/Prog/Cno102B_TopInst.v); its
     premises: the class-3 frame call at ARcf (FCm3xm, on the cut), __asan_memset (PRowSet, on the cut), parse_noting
     (above), fuzz_alloc_ran_out (on the cut), same (SameB_final.same_holds_B_TfibBx,
     lib/B/Prog/SameB_final.v, with the strcmp row PSstrRo.ps_strcmp_xrom_xs_B and the bcmp row), free
     (the export's row), pj_free (H_text_pj_free_B, below), __asan_set_shadow_f5
     (FCxmCfxB.set_shadow_f5_contract_xm_cfx_B, on the cut) and padded (
     Padded102B_Inst.padded_B_at_PI_prog_B, lib/B/Prog/Padded102B_Inst.v: the kit's tpadded_specX verbatim, its
     trace from clause 5; premises the malloc row, __asan_memcpy and __asan_memset at iface_ARx);
   - check_reject_clean_starved: CrsTopBp.crs_holds_Bp (commit d664902eef28); the guarded
     dead-pj_parse conjunct is a conjunct of the kit's tpj_parse_specX itself (lib/A/PRH_FnPj.v), so the stand-in
     CrsPjpDeadAp.tpj_parse_specX_K0dead and the Section hypothesis K0_DEAD_PJPARSE are gone: crs_holds_Bp is cited
     with no K0_DEAD_PJPARSE argument and takes pj_parse's text as it is; its callee premises: check_reject_clean and
     the ledger accessors live / count / fail / ran_out (in this tree), the class-1 frame call
     (FCxmCfxB.stack_malloc1_contract_xm_cfx_B, on the cut), and the
     texts pj_parse (open), fuzz_pick (FuzzPickB.fuzz_pick_holds_B, lib/B/Prog/FuzzPickB.v,
     no premise), fuzz_free, fuzz_free_null and pj_write (below);
   - read_members: read_members_Bp4.read_members_holds_Bp4 (lib/B/Prog/read_members_Bp4.v);
   - pj_free: pj_free_iface.tpj_free_specX_B_preset_iface (over lib/B/Prog/pj_free_top.v,
     whose pf_wit_univ cites the kit's PRH_Witness.prh_univ_closure_witness_B);
     its premises __asan_memset (PRowSet.prow_asan_memset_xm_B, on the cut) and fuzz_free (below);
   - fuzz_free: FuzzFreeB.fuzz_free_holds_B (on the cut) at TfibB'; its premises: the free row (H_afree_realizes_cf_B),
     __asan_unpoison_memory_region (CfPoisonB102.preset_aunpoison_cf_B102 on the cut, at the ARcf laws and TfibB_syms;
     its stand-in poison_next_vis_cf is the top premise H_poison_next_vis_cf_B, owner: a Theorem Labs lane), PAL
     (PALibB.exvi_eh_palib), pal_pst_ok (FuzzAllocAccInstB102.acc_pal_pst_ok_B), pal_unpoison (vm_compute) and TS
     (YD2l.TfibB_syms);
   - fuzz_free_null: FuzzFreeNullB.fuzz_free_null_holds_B (lib/B/Prog/FuzzFreeNullB.v, fuzz_free's NULL-only text) at
     TfibB'; its premises are among fuzz_free's and close the same way;
   - pj_write: PRW_pj_writeB_Inst.pj_write_holds_B_inst (lib/B/Prog/PRW_pj_writeB_Inst.v);
     its premises: write_value (WriteValueB_Inst.write_value_holds_B, lib/B/Prog/WriteValueB_Inst.v),
     put, fuzz_free (above) and pjw_ARGCNT (PresetRoomCounts.counts_of_room_pos_rl,
     lib/Spec/PresetRoomCounts.v:60, as lib/AU/Prog/Ent102DrvTopB3.v drv3_argcnt does);
     write_value's premises: put, put_string (PutStringB_SnpWit.put_string_holds_B_owner,
     lib/B/Prog/PutStringB_SnpWit.v: put, the class-0 frame call (FCm01xm at ARcf lifted by
     astack_malloc_realizes_xm_conj, as FCxmCfxB does), __asan_memcpy, and the __wrap_snprintf row at K := 8160
     (PSnpRowB.snprintf_row_B_inst, lib/B/Prog/PSnpRowB.v, no premise)) and
     indent (IndentB_Top.indent_holds_B,
     lib/B/Prog/IndentB_Top.v, over the shared writer helpers lib/A/Prog/S7a_WriterRet.v / S7a_WriterLive.v); put is
     PutB.put_holds_B (lib/B/Prog/PutB.v) with __asan_memcpy and fuzz_realloc
     (FuzzReallocB_p102.fuzz_realloc_holds_B', lib/B/Prog/FuzzReallocB_p102.v; its own
     premises: own (OwnB_p102.own_holds_B, row AL6, on the cut; its poison row
     CfPoisonB102.preset_apoison_cf_B102), fuzz_malloc (FuzzMallocB_p102_holds.fuzz_malloc_holds_B, row
     AL2, lib/B/Prog/FuzzMallocB_p102_holds.v; the malloc row, own and TS) and the realloc row (the top premise
     H_arealloc_B); unpoison, PAL, pal_pst_ok close as for fuzz_free, and pal_errno_relro by
     CfAroPresetB.errno_relro_preset_AU at TfibB_syms);
   - fuzz_alloc_most: FuzzAllocMostBp.fuzz_alloc_most_holds_B, the cut's own copy (the same statement as
     the row AL5 core walk's FuzzAllocMostBp.v (sha256 5753fedfd5b5; internal record), marked not for this integration), PST_unowned by
     PwPstUnownedB.pst_unowned_TfibB;
   - fuzz_alloc_ran_out / _reset: FuzzAllocAccInstB102's _B_inst corollaries (on the cut);
   - check_bounded_alloc (CheckBoundedAllocBInst), check_reject_clean (CrcBInstLive through
     PRW_AfnBridgeBProg.v, image shadow proved there), the four ledger accessors (BridgeB), the frame release
     (astack_free_law_ok_cf);
   - the bcmp row: PRowCmp.pr_bcmp_xm_B_pc at iface_ARx (laws AR_laws_x_xs, TfibB_syms), its pc equal to
     the listing's by vm_compute (as ExvB_Inst does);
   - the frame call in the record's form (ARx := ARcf, classes 0 / 1 / 3): the FrameXm102 rows
     FCm01xm.stack_malloc0/1_contract_xm and FCm3xm.stack_malloc3_contract_xm at fs_iface_ARcf (FCxmCfxB's _cfx_B
     corollaries are at ARcf /\ xs_placed_cf, not the record's ARcf);
   - the export's memcpy / memset rows: PRowCpy.prow_memcpy_icpt_xm_B and PRowSet.prow_memset_icpt_xm_B
     at ARcf (laws AR_laws_x_cf);
   - start-up, driver walk, interceptor and printf / exit sites, the non-primary room and the universe closure: inside
     the export.
   NOT CITED: check_round_trip. The crt102_topB_TfibB this file was written against (the version Crt102TopB.v (sha256 0e8e2bd9b046; internal record) of
   lib/B/Prog/Crt102TopB.v:795) ends in Abort: it is not a theorem. The closed form there is crt102_topB_open_TfibB with
   the antecedent CRT_B_SEAM_OPEN and 20 Section hypotheses; H_text_check_round_trip_B stays.
   THE PROOF of the top: split on argv's shape and on the file system's lookup; the room arm is the export, the no-room
   arm payload_refusal_B; the SPECX arm closes with HaltsTFIB.v's presetAU_SPECX_shape_ok (exits 0 / 2), and
   HaltsTop.v's preset_asan_ubsan_halts_of_tfib gives the statement. The open names and their owners are the Section
   hypotheses below. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import AsanUbsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO09 YM05 YO06 YI16 YCbqG YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0ncf YG0dcf YG0tcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2l YB1v HaltsKitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc PRH_FnCheck PRH_FnPj PRH_FnEx PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB PresetCfnB PresetTFIBAU.
(* aread_check_stmt_cf, the read interceptor's check statement the export takes (lib/AU/PresetD1preB.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PresetD1preB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import HaltsTFIB HaltsTop.
(* the B' closed room export and its statement file (np_live_B, PAYLOAD_ROOM_dec_stmt), cited qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetDrvTopBStmt PresetD2pBPf.
(* the B' seam and its instance values *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Ent102InstB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require Ent102SeamB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.Prog Require PRW_AfnBridgeBProg.
(* the program walks cited for the callee record *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CheckBoundedAllocBInst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PRW_AfnBridgeB PwPstUnownedB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PN102BTop Caw102B_Img ex_ws_cf ExvB_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require read_members_Bp4 pj_free_iface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzAllocAccInstB102 FuzzAllocMostBp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Cno102B_TopInst SameB_defs SameB_final.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrsTopBp FuzzPickB Padded102B_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzFreeB FuzzFreeNullB PutB IndentB_Top.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PutStringB_SnpWit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require WriteValueB_Inst PRW_pj_writeB PRW_pj_writeB_Inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require PSnpRowB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require FuzzReallocB_p102 OwnB_p102 FuzzMallocB_p102_holds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomCounts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfPoisonB102 CfAroPresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfHp YGcallSnp YGcallSnpCk YE22 YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep YGcfRoomLive.
(* the runtime rows: bcmp, memcpy / memset, the frame-area classes *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PRowCmp PRowCpy PRowSet FCm01xm FCm3xm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require FCxmCfxB PSstrRo.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require FCifaceCf YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YGcfMallocComposeKeep.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section closed.
(* init_config reads the FP state at the start-up one, as HaltsTFIB.v's TFIB_T_AU_H and the export's
   TFIB_T_room_all_concl_B (PresetDrvTopBStmt.v) do *)
#[local] Existing Instance YK11.fx0.
(* the image's CfImg record CfImg_B (lib/AU/CfImgB.v), as the interface's texts and the export take it *)
#[local] Existing Instance CfImg_B.
(* preset's CfParams and the room-live instance prh_room_live_a8 as instances (the own / fuzz_malloc texts below
   leave ci, cp and RL implicit, as the walks do) *)
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_room_live_a8.

(* ---------------------------------------------------------------------- *)
(* A. The instance (header): PAYLOAD_ROOM, sm, np, A_MOD_AT / A_STAMP are cited; XM_LIB / XN_LIB := fun _ => 0. *)

#[local] Abbreviation PAB r := (PI_prog_B (rc := r)).
#[local] Abbreviation ARi r := (iface_ARx (rc := r) (L := B_prog_listing) (PA := PAB r) TfibB).
#[local] Abbreviation RLX := (@prh_room_live_a8 CfParams_preset).
#[local] Abbreviation SEGS_B r := (@pa_segs r B_prog_listing (PAB r)).
#[local] Abbreviation NPB := PresetDrvTopBStmt.np_live_B.
#[local] Abbreviation PRT := (fun _ : list byte => True).
#[local] Abbreviation SMB := ReaderRes.jr_strtod.
#[local] Abbreviation AMOD := Ent102InstB.ia_mod_at.
#[local] Abbreviation ASTAMP := Ent102InstB.ia_stamp.
(* the per-call meter allowances: the trivial meter ameter_triv never reads them and the top's type does not mention
   them (round 2's Check printed them as `_` binders), so any value instantiates them *)
#[local] Abbreviation XLIB0 := (fun _ : Z => 0).

(* ---------------------------------------------------------------------- *)
(* B0. The runtime rows at the instance, from results in this tree. *)
(* the laws at the record's relation iface_ARx (as pj_free_iface.v pf_wit_laws_iface) *)
Lemma laws_iface_B : forall rc : YM05.RunCeil,
  YCbqG.AR_laws_x (SEGS_B rc) TfibB (ARi rc) (@cf_head CfParams_preset).
Proof.
intros rc. unfold iface_ARx.
exact (YGcallcf.AR_laws_x_xs (cp := CfParams_preset) (SEGS_B rc) TfibB
  (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) (SEGS_B rc) TfibB)).
Qed.

(* the bcmp wrapper's row at iface_ARx: PRowCmp.pr_bcmp_xm_B_pc, its pc equal to the listing's by vm_compute *)
Lemma bcmp_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  YGcallMxmn.abcmp_realizes_xm (fx := fy) (SEGS_B rc) TfibB (ARi rc) (@pa_sigma rc B_prog_listing (PAB rc) AS___wrap_bcmp).
Proof.
intros rc fy.
pose proof (PRowCmp.pr_bcmp_xm_B_pc (fx := fy) (rc := rc) TfibB (ARi rc) _ (laws_iface_B rc) YD2l.TfibB_syms) as H.
match type of H with YGcallMxmn.abcmp_realizes_xm _ _ _ ?p =>
  replace (@pa_sigma rc B_prog_listing (PAB rc) AS___wrap_bcmp) with p;
    [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
Qed.

(* __asan_memset at iface_ARx (pj_free's premise): PRowSet.prow_asan_memset_xm_B, pc by vm_compute *)
Lemma asan_memset_iface_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fy) (SEGS_B rc) TfibB (ARi rc) OSet
    (@pa_sigma rc B_prog_listing (PAB rc) AS___asan_memset).
Proof.
intros rc fy.
pose proof (PRowSet.prow_asan_memset_xm_B (fx := fy) (rc := rc) TfibB (ARi rc) _ (laws_iface_B rc) YD2l.TfibB_syms)
  as H.
match type of H with YGcallMxmn.aintrin_realizes_xm _ _ _ _ ?p =>
  replace (@pa_sigma rc B_prog_listing (PAB rc) AS___asan_memset) with p;
    [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
Qed.

(* __asan_memcpy at iface_ARx (padded's premise): PRowCpy.prow_asan_memcpy_xm_B, pc by vm_compute *)
Lemma asan_memcpy_iface_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fy) (SEGS_B rc) TfibB (ARi rc) OCpy
    (@pa_sigma rc B_prog_listing (PAB rc) AS___asan_memcpy).
Proof.
intros rc fy.
pose proof (PRowCpy.prow_asan_memcpy_xm_B (fx := fy) (rc := rc) TfibB (ARi rc) _ (laws_iface_B rc) YD2l.TfibB_syms)
  as H.
match type of H with YGcallMxmn.aintrin_realizes_xm _ _ _ _ ?p =>
  replace (@pa_sigma rc B_prog_listing (PAB rc) AS___asan_memcpy) with p;
    [exact H | apply Z.eqb_eq; vm_compute; reflexivity] end.
Qed.

(* the export's memcpy / memset rows at ARcf: the PRowCpy / PRowSet interceptor rows with the ARcf laws *)
Lemma aintrin_cpy_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OCpy (pc_wrap_memcpy (as_code TfibB)).
Proof.
intros rc fy.
exact (PRowCpy.prow_memcpy_icpt_xm_B (fx := fy) (rc := rc) TfibB _ _
  (YGcallcf.AR_laws_x_cf (cp := CfParams_preset) tfibsegs TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs TfibB)) YD2l.TfibB_syms).
Qed.
Lemma aintrin_set_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcallMxmn.aintrin_realizes_xm (fx := fx) tfibsegs TfibB
    (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) OSet (pc_wrap_memset (as_code TfibB)).
Proof.
intros rc fy.
exact (PRowSet.prow_memset_icpt_xm_B (fx := fy) (rc := rc) TfibB _ _
  (YGcallcf.AR_laws_x_cf (cp := CfParams_preset) tfibsegs TfibB
     (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs TfibB)) YD2l.TfibB_syms).
Qed.

(* the record's frame call (PresetCfnB.v astack_malloc_realizes_cfm: the keep form at ARcf) for the unit's classes
   0 / 1 / 3: the FCm01xm / FCm3xm rows at fs_iface_ARcf of the ARcf laws *)
Lemma stack_malloc_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState) (cid : Z),
  In cid (@cf_fs_classes CfParams_preset) ->
  astack_malloc_realizes_cfm (rc := rc) (fx := fy) tfibsegs TfibB cid.
Proof.
intros rc fy cid Hin.
assert (E : @cf_fs_classes CfParams_preset = [0; 1; 3]) by reflexivity.
rewrite E in Hin.
destruct Hin as [Hc | [Hc | [Hc | Hc]]].
- subst cid. exact (FCm01xm.stack_malloc0_contract_xm (fx := fy) TfibB _
    (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs TfibB)) (proj2 YD2l.TfibB_pair)).
- subst cid. exact (FCm01xm.stack_malloc1_contract_xm (fx := fy) TfibB _
    (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs TfibB)) (proj2 YD2l.TfibB_pair)).
- subst cid. exact (FCm3xm.stack_malloc3_contract_xm (fx := fy) TfibB _
    (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs TfibB
       (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs TfibB)) (proj2 YD2l.TfibB_pair)).
- destruct Hc.
Qed.

(* same at iface_ARx (check_no_overread's HSAME): SameB_final.same_holds_B_TfibBx at ARcf /\ xs_placed_cf,
   its two runtime rows from the strcmp row (PSstrRo.ps_strcmp_xrom_xs_B) and the bcmp row, each pc equal to
   same's by vm_compute (as ExvB_Inst does) *)
Lemma same_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnEx.tsame_specX (fx := fz) (rc := rc) (cp := CfParams_preset) (PI := preset_prh_img) (RL := RLX)
    (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head DOC_D.
Proof.
intros rc fz.
pose proof (PSstrRo.ps_strcmp_xrom_xs_B (fx := fz) (rc := rc) (cp := CfParams_preset) TfibB YD2l.TfibB_syms
  B_prog_relro_lo B_prog_relro_hi) as HS.
pose proof (PRowCmp.pr_bcmp_xm_B_pc (fx := fz) (rc := rc) TfibB (ARi rc) _ (laws_iface_B rc) YD2l.TfibB_syms) as HB.
refine (SameB_final.same_holds_B_TfibBx (fx := fz) (rc := rc) preset_sink_head _ _ DOC_D).
- match type of HS with YGcallMxmn.astrcmp_realizes_xrom _ _ _ _ _ ?p =>
    replace SameB_defs.SMB_STRCMP with p; [exact HS | apply Z.eqb_eq; vm_compute; reflexivity] end.
- match type of HB with YGcallMxmn.abcmp_realizes_xm _ _ _ ?p =>
    replace SameB_defs.SMB_BCMP with p; [exact HB | apply Z.eqb_eq; vm_compute; reflexivity] end.
Qed.

(* ---------------------------------------------------------------------- *)
(* B. The callee texts with no cited walk at the record's form. OWNER of each: the signed B' walk of the function. *)
Hypothesis H_text_check_round_trip_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  @PRH_FnCheck.tcheck_round_trip_specX fy rc CfImg_B CfParams_preset preset_prh_img RLX B_prog_listing (PAB rc)
    TfibB (ARi rc) preset_sink_head iface_ctx0 AMOD ASTAMP.
(* the premises of the cited walks that no result in this tree states at the record's form: pj_parse (parse_noting's
   HPJ, check_reject_clean_starved's HT_pj_parse) *)
Hypothesis H_text_pj_parse_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState) (CW : list (list Z)),
  PRH_FnPj.tpj_parse_specX (fx := fy) (rc := rc) (cp := CfParams_preset) (PI := preset_prh_img)
    (RL := RLX) (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head iface_ctx0 CW.
(* fuzz_realloc's realloc wrapper row (FuzzReallocB_p102.v Section f, AREAL_cf): the primed _k row with the memnorm
   keep (YGcfInstReallocKKeep.v), at every float state, ghost set Hp and headroom k; AllocAssembleB.v:62 proves it, this file keeps it open; OWNER
   Theorem Labs *)
Hypothesis H_arealloc_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState) (Hp : list Z) (k : nat),
  YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (fx := fx) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    (@YC4aP.pa_segs rc B_prog_listing (@PI_prog_B rc)) TfibB Hp
    (@YC4aP.pa_sigma rc B_prog_listing (@PI_prog_B rc) YPsym.AS___wrap_realloc) k.
(* __asan_unpoison_memory_region's stand-in poison_next_vis_cf (CfPoisonB102.v Section f, the cut's blob); OWNER
   two Theorem Labs work streams: another CfPoisonB102.v (sha256 d92782fd7ba5; internal record) cites CfApiPreset.poison_next_vis_cf instead *)
Hypothesis H_poison_next_vis_cf_B : forall (rc : YM05.RunCeil) ly S Hp (W : world tfibsegs) mem md p n,
  ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB ly S Hp W mem md -> In (p, n) (ablocks TfibB ly S) ->
  req_size n = cf_head -> aview tfibsegs (w_H W) mem (shadow_addr (p + cf_head)) <> None.
(* the export's allocator rows (section D's other names), here because the cited check_as_written walk takes them:
   malloc at EVERY float state (the walk's form; the export takes it in the same form, passed whole below) and free;
   OWNER: two Theorem Labs work streams. Both are named in their keep forms (YGcfMallocComposeKeep: the leaf with the
   memnorm keep at its end), the forms the cited walks and the export take: malloc amalloc_realizes_cf_keep, free the
   primed row afree_realizes_cf_rh_keep (a free re-hides shadow) *)
Hypothesis H_amalloc_realizes_cf_keep_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.amalloc_realizes_cf_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.
Hypothesis H_afree_realizes_cf_B : forall (rc : YM05.RunCeil) (fx : YK11.FPState),
  YGcfMallocComposeKeep.afree_realizes_cf_rh_keep (fx := fx) (cp := CfParams_preset) tfibsegs TfibB.

(* check_reject_clean: the SIGNED B' walk through PRW_AfnBridgeBProg.v, at the bcmp row bcmp_B *)
Lemma pcc_check_reject_clean_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  @PRH_FnCheck.tcheck_reject_clean_specX fy rc CfParams_preset preset_prh_img RLX B_prog_listing (PAB rc)
    TfibB (ARi rc) preset_sink_head.
Proof.
intros rc fy.
exact (PRW_AfnBridgeBProg.pcc_check_reject_clean_of_walk (fx := fy) (rc := rc) (bcmp_B rc fy)).
Qed.

(* parse_noting at the record's form (cited twice: as the record field and as check_no_overread's premise HPN) *)
Lemma pn_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  @PRH_FnCheck.tparse_noting_specX fz rc CfImg_B CfParams_preset preset_prh_img RLX B_prog_listing (PAB rc)
    TfibB (ARi rc) preset_sink_head iface_ctx0.
Proof.
intros rc fz.
exact (PN102BTop.tparse_noting_specX_TfibB (fx := fz) (rc := rc) (ci := CfImg_B) (SK := preset_sink_head) iface_ctx0
  (PRW_AfnBridgeB.pcc102_fuzz_alloc_live_of_walk (rc := rc) TfibB fz)
  (H_text_pj_parse_B rc fz)
  (fun fw => FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst (fx := fw) (rc := rc) (SK := preset_sink_head))
  (pcc_check_reject_clean_B rc)).
Qed.
(* __asan_unpoison_memory_region at TfibB': CfPoisonB102.preset_aunpoison_cf_B102 (the cut's blob), at
   the ARcf laws, TfibB_syms and its stand-in H_poison_next_vis_cf_B *)
Lemma aunpoison_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  @YGcfHp.aunpoison_realizes_cf fz rc CfImg_B CfParams_preset tfibsegs TfibB.
Proof.
intros rc fz.
pose proof (YG0lawscf.AR_laws_ok_cf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) as LAWS.
pose proof (H_poison_next_vis_cf_B rc) as POIS.
eapply (CfPoisonB102.preset_aunpoison_cf_B102 (fx := fz) (rc := rc) TfibB);
  first [ exact LAWS | exact YD2l.TfibB_syms | exact POIS ].
Qed.
(* __asan_poison_memory_region at TfibB': CfPoisonB102.preset_apoison_cf_B102 (the cut's blob), at the
   ARcf laws, TfibB_syms and the stand-in H_poison_next_vis_cf_B *)
Lemma apoison_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  @YGcfHp.apoison_realizes_cf fz rc CfImg_B CfParams_preset tfibsegs TfibB.
Proof.
intros rc fz.
pose proof (YG0lawscf.AR_laws_ok_cf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) as LAWS.
pose proof (H_poison_next_vis_cf_B rc) as POIS.
eapply (CfPoisonB102.preset_apoison_cf_B102 (fx := fz) (rc := rc) TfibB);
  first [ exact LAWS | exact YD2l.TfibB_syms | exact POIS ].
Qed.
(* own at the record's form: OwnB_p102.own_holds_B (row AL6, on the cut) at TfibB' (the kit's town_specX at
   ARcfx = ARcf /\ xs_placed_cf, the record's iface_ARx, and SK := preset_sink_head); PAL, pal_pst_ok, pal_poison (the
   poison entry's pc, by vm_compute) and the poison row apoison_B *)
Lemma own_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnAlloc.town_specX (fx := fz) (rc := rc) (PI := preset_prh_img) (L := B_prog_listing) (PA := PAB rc)
    TfibB (ARi rc) preset_sink_head.
Proof.
intros rc fz.
eapply (OwnB_p102.own_holds_B (fx := fz) (rc := rc) (ci := CfImg_B) (SK := preset_sink_head) TfibB);
  first [ exact PALibB.exvi_eh_palib | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B | exact (apoison_B rc fz)
        | (apply Z.eqb_eq; vm_compute; reflexivity) ].
Qed.
(* fuzz_malloc at the record's form: FuzzMallocB_p102_holds.fuzz_malloc_holds_B (row AL2,
   lib/B/Prog/FuzzMallocB_p102_holds.v) at TfibB'; PAL, pal_pst_ok, the malloc row in its keep form, own (own_B) and
   TS (YD2l.TfibB_syms) *)
Lemma fuzz_malloc_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnAlloc.tfuzz_malloc_specX (fx := fz) (rc := rc) (PI := preset_prh_img) (L := B_prog_listing) (PA := PAB rc)
    TfibB (ARi rc) preset_sink_head.
Proof.
intros rc fz.
eapply (FuzzMallocB_p102_holds.fuzz_malloc_holds_B (fx := fz) (rc := rc) (SK := preset_sink_head)
  TfibB);
  first [ exact PALibB.exvi_eh_palib | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B
        | exact (H_amalloc_realizes_cf_keep_B rc fz) | exact (own_B rc fz) | exact YD2l.TfibB_syms ].
Qed.
(* fuzz_free at the record's form: FuzzFreeB.fuzz_free_holds_B at TfibB', its premises from this tree (header) *)
Lemma fuzz_free_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnAlloc.tfuzz_free_specX (fx := fz) (rc := rc) (cp := CfParams_preset) (PI := preset_prh_img) (RL := RLX)
    (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head.
Proof.
intros rc fz.
eapply (FuzzFreeB.fuzz_free_holds_B (fx := fz) (rc := rc) (SK := preset_sink_head) TfibB);
  first [ exact (H_afree_realizes_cf_B rc fz) | exact (aunpoison_B rc fz) | exact PALibB.exvi_eh_palib
        | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B | (apply Z.eqb_eq; vm_compute; reflexivity)
        | exact YD2l.TfibB_syms ].
Qed.
(* fuzz_free's NULL-only text at the record's form (check_reject_clean_starved's HT_fuzz_free_null):
   FuzzFreeNullB.fuzz_free_null_holds_B at TfibB', its premises closed as for fuzz_free *)
Lemma fuzz_free_null_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnAlloc.tfuzz_free_null_specX (fx := fz) (rc := rc) (PI := preset_prh_img) (L := B_prog_listing) (PA := PAB rc)
    TfibB (ARi rc) preset_sink_head.
Proof.
intros rc fz.
eapply (FuzzFreeNullB.fuzz_free_null_holds_B (fx := fz) (rc := rc) (SK := preset_sink_head) TfibB);
  first [ exact (H_afree_realizes_cf_B rc fz) | exact (aunpoison_B rc fz) | exact PALibB.exvi_eh_palib
        | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B | (apply Z.eqb_eq; vm_compute; reflexivity)
        | exact YD2l.TfibB_syms ].
Qed.
(* fuzz_realloc at the record's form: FuzzReallocB_p102.fuzz_realloc_holds_B' at TfibB' (the kit's
   tfuzz_realloc_specX at ARcf /\ xs_placed_cf = iface_ARx), its premises own (own_B), fuzz_malloc (fuzz_malloc_B), the
   realloc row (named above), unpoison (aunpoison_B), PAL and pal_pst_ok (as for fuzz_free) and pal_errno_relro
   (CfAroPresetB.errno_relro_preset_AU at TfibB_syms) *)
Lemma fuzz_realloc_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnAlloc.tfuzz_realloc_specX (fx := fz) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (PI := preset_prh_img)
    (RL := RLX) (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head.
Proof.
intros rc fz.
eapply (FuzzReallocB_p102.fuzz_realloc_holds_B' (fx := fz) (rc := rc) (SK := preset_sink_head) TfibB);
  first [ exact (own_B rc fz) | exact (fuzz_malloc_B rc fz) | exact (aunpoison_B rc fz)
        | exact (H_arealloc_B rc fz) | exact PALibB.exvi_eh_palib | exact FuzzAllocAccInstB102.acc_pal_pst_ok_B
        | exact (CfAroPresetB.errno_relro_preset_AU TfibB YD2l.TfibB_syms) ].
Qed.
(* pj_free at the record's form (the record field and check_no_overread's HPJF) *)
Lemma pjf_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  @PRH_FnPj.tpj_free_specX fz rc CfImg_B CfParams_preset preset_prh_img RLX B_prog_listing (PAB rc)
    TfibB (ARi rc) preset_sink_head iface_ctx0 DOC_D.
Proof.
intros rc fz.
exact (pj_free_iface.tpj_free_specX_B_preset_iface (fx := fz) (rc := rc) (ci := CfImg_B) (RL := RLX)
  (SK := preset_sink_head) (fuzz_free_B rc fz) (asan_memset_iface_B rc fz) iface_ctx0 DOC_D).
Qed.
(* put at the record's form, every context set: PutB.put_holds_B with __asan_memcpy and fuzz_realloc *)
Lemma put_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState) (CTX0 : list (list Z)),
  PRH_FnWriter.tput_specX (fx := fz) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (PI := preset_prh_img)
    (RL := RLX) (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head CTX0.
Proof.
intros rc fz CTX0.
eapply (PutB.put_holds_B (fx := fz) (rc := rc) (SK := preset_sink_head));
  first [ exact (fuzz_realloc_B rc fz) | exact (asan_memcpy_iface_B rc fz) ].
Qed.
(* indent at the record's form: IndentB_Top.indent_holds_B with put *)
Lemma indent_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnWriter.tindent_specX (fx := fz) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (PI := preset_prh_img)
    (RL := RLX) (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head iface_ctx0.
Proof.
intros rc fz.
eapply (IndentB_Top.indent_holds_B (fx := fz) (rc := rc) (SK := preset_sink_head));
  first [ exact (put_B rc fz) ].
Qed.
(* the class-0 frame call at iface_ARx (put_string's premise): the FCm01xm row at ARcf, lifted to
   ARcf /\ xs_placed_cf by astack_malloc_realizes_xm_conj (as FCxmCfxB.v does for classes 1 and 3) *)
Lemma stack_malloc0_iface_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  YGcallMxmn.astack_malloc_realizes_xm (fx := fz) (SEGS_B rc) TfibB (ARi rc) 0.
Proof.
intros rc fz.
exact (YGcallMxmn.astack_malloc_realizes_xm_conj (fx := fz) tfibsegs TfibB
  (ARcf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB) (fun ly S => xs_placed_cf ly S) 0
  YGcallScf.xs_placed_cf_set_fs
  (FCm01xm.stack_malloc0_contract_xm (fx := fz) TfibB _
     (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs TfibB
        (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs TfibB)) (proj2 YD2l.TfibB_pair))).
Qed.
(* put_string's __wrap_snprintf row at the owner's values, K := 8160 (the root's window):
   PSnpRowB.snprintf_row_B_inst; its cr PSnpRowB.snr_cr is put_string's psn_cr by its body, rewritten first *)
Lemma snprintf_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  YGcallSnp.asnprintf_realizes_xrom (fx := fz) (SEGS_B rc) TfibB (ARi rc)
    (@pa_relro_lo rc B_prog_listing (PAB rc)) (@pa_relro_hi rc B_prog_listing (PAB rc))
    (YGcallSnpCk.FF_esc (@pa_lo rc B_prog_listing (PAB rc)) YE22.A_GOT_CANARY) 8160
    YE22.A_GOT_CANARY YE22.V_GOT_CANARY (@pa_lo rc B_prog_listing (PAB rc)) (@pa_hi rc B_prog_listing (PAB rc))
    (PutStringB_SnpWit.psn_cr (rc := rc)) (@pa_sigma rc B_prog_listing (PAB rc) AS___wrap_snprintf).
Proof.
intros rc fz.
assert (E : PSnpRowB.snr_cr (rc := rc) = PutStringB_SnpWit.psn_cr (rc := rc)) by reflexivity.
rewrite <- E.
exact (PSnpRowB.snprintf_row_B_inst (rc := rc) 8160 (Z.le_refl _) fz).
Qed.
(* put_string at the record's form: PutStringB_SnpWit.put_string_holds_B_owner at K := 8160 (psn_K_le) *)
Lemma put_string_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnWriter.tput_string_specX (fx := fz) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset) (PI := preset_prh_img)
    (RL := RLX) (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head iface_ctx0.
Proof.
intros rc fz.
exact (PutStringB_SnpWit.put_string_holds_B_owner (rc := rc) (SK := preset_sink_head) iface_ctx0
  (fun fw => put_B rc fw iface_ctx0) (stack_malloc0_iface_B rc) (asan_memcpy_iface_B rc) 8160
  PutStringB_SnpWit.psn_K_le (snprintf_B rc) fz).
Qed.
(* write_value at the record's form, every depth: WriteValueB_Inst.write_value_holds_B with put, put_string, indent *)
Lemma write_value_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState) (n : nat),
  PRH_FnWriter.twrite_value_specX (fx := fz) (rc := rc) (ci := CfImg_B) (cp := CfParams_preset)
    (PI := preset_prh_img) (RL := RLX) (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head
    iface_ctx0 n.
Proof.
intros rc fz n.
exact (WriteValueB_Inst.write_value_holds_B (fx := fz) (rc := rc) preset_sink_head iface_ctx0
  (fun fw => put_B rc fw iface_ctx0) (put_string_B rc) (indent_B rc) n).
Qed.
(* pj_write at the record's form (check_reject_clean_starved's HT_pj_write): PRW_pj_writeB_Inst.pj_write_holds_B_inst *)
Lemma pj_write_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  PRH_FnWriter.tpj_write_specX (fx := fy) (rc := rc) (cp := CfParams_preset) (PI := preset_prh_img) (RL := RLX)
    (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head iface_ctx0 DOC_D.
Proof.
intros rc fy.
refine (PRW_pj_writeB_Inst.pj_write_holds_B_inst (fx := fy) (rc := rc) preset_sink_head iface_ctx0
  (write_value_B rc fy) (fun fw => put_B rc fw iface_ctx0) (fuzz_free_B rc) DOC_D _).
(* pjw_ARGCNT: the class-24 live count at a model-run position, the second conjunct of
   PresetRoomCounts.counts_of_room_pos_rl (the tactic of Ent102DrvTopB3.v drv3_argcnt) *)
intros; hnf; intros;
  lazymatch goal with |- YGcfRoomLive.ccnt24 ?S' <= _ =>
    match goal with Hp : PresetRoomPos.iface_room_pos _ _ _ _ _ _ S' |- _ =>
      exact (proj2 (PresetRoomCounts.counts_of_room_pos_rl _ _ _ _ _ _ _ Hp)) end end.
Qed.
(* padded at the record's form (check_no_overread's HPAD): padded_B_at_PI_prog_B (the kit's tpadded_specX
   verbatim at RL := pd_RL = prh_room_live_a8 CfParams_preset, ARx := ARcf /\ xs_placed_cf = iface_ARx), its premises
   TfibSyms (YD2l.TfibB_syms), the malloc row in its keep form, the __asan_memcpy / __asan_memset rows at iface_ARx and
   the read-only link at ci := CfImg_B (Padded102B_Inst.pdi_aro_link_B) *)
Lemma padded_text_B : forall (rc : YM05.RunCeil) (fz : YK11.FPState),
  PRH_FnCheck.tpadded_specX (fx := fz) (rc := rc) (cp := CfParams_preset) (PI := preset_prh_img) (RL := RLX)
    (L := B_prog_listing) (PA := PAB rc) TfibB (ARi rc) preset_sink_head iface_ctx0.
Proof.
intros rc fz.
exact (Padded102B_Inst.padded_B_at_PI_prog_B (fx := fz) (rc := rc) (ci := CfImg_B) (SK := preset_sink_head) TfibB
  YD2l.TfibB_syms (H_amalloc_realizes_cf_keep_B rc fz) (asan_memcpy_iface_B rc fz) (asan_memset_iface_B rc fz)
  (Padded102B_Inst.pdi_aro_link_B (rc := rc) TfibB YD2l.TfibB_syms) iface_ctx0).
Qed.

(* the B' callee record at TfibB', at every run ceiling and float state, by field name *)
Lemma pcc_all_B : forall (rc : YM05.RunCeil) (fy : YK11.FPState),
  preset_callee_contracts (rc := rc) (L := B_prog_listing) (PA := PAB rc) (ci := CfImg_B) (fx := fy)
    TfibB AMOD ASTAMP.
Proof.
intros rc fy. exact {|
  pcc_check_no_overread := fun fz =>
    Cno102B_TopInst.cnb_B_top_inst (fx := fz) (rc := rc) (SK := preset_sink_head) iface_ctx0
      (fun fw => FCm3xm.stack_malloc3_contract_xm (fx := fw) TfibB _
         (FCifaceCf.fs_iface_ARcf (cp := CfParams_preset) tfibsegs TfibB
            (YG0lawscf.AR_laws_ok_cf (cp := CfParams_preset) tfibsegs TfibB)) (proj2 YD2l.TfibB_pair))
      (asan_memset_iface_B rc)
      (padded_text_B rc)
      (pn_B rc)
      (fun fw => FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst (fx := fw) (rc := rc) (SK := preset_sink_head))
      (same_B rc)
      (H_afree_realizes_cf_B rc)
      (pjf_B rc)
      (FCxmCfxB.set_shadow_f5_contract_xm_cfx_B (rc := rc) (cp := CfParams_preset) TfibB YD2l.TfibB_syms);
  pcc_parse_noting := pn_B rc;
  pcc_check_bounded_alloc := fun fz =>
    CheckBoundedAllocBInst.check_bounded_alloc_holds_B_inst_xs (fx := fz) (rc := rc) preset_sink_head;
  pcc_check_as_written := fun fz =>
    Caw102B_Img.caw_B_top_inst (fx := fz) (rc := rc) (SK := preset_sink_head)
      (fun fw => ExvB_Inst.ex_value_holds_B_closed (rc := rc) (ci := CfImg_B) (RL := RLX) preset_sink_head DOC_D fw)
      (fun fw => ex_ws_cf.ex_ws_holds_B (fx := fw) (rc := rc) preset_sink_head)
      (fun fw => FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst (fx := fw) (rc := rc) (SK := preset_sink_head))
      (H_afree_realizes_cf_B rc) (H_amalloc_realizes_cf_keep_B rc) iface_ctx0;
  pcc_check_reject_clean := pcc_check_reject_clean_B rc;
  pcc_check_reject_clean_starved := fun fz =>
    CrsTopBp.crs_holds_Bp (fx := fz) (rc := rc) (ci := CfImg_B) (RL := RLX) (SK := preset_sink_head)
      iface_ctx0
      (pcc_check_reject_clean_B rc)
      (PRW_AfnBridgeB.pcc102_fuzz_alloc_count_of_walk (rc := rc) TfibB)
      (fun fw => FuzzAllocAccInstB102.fuzz_alloc_fail_holds_B_inst (fx := fw) (rc := rc) (SK := preset_sink_head))
      (PRW_AfnBridgeB.pcc102_fuzz_alloc_live_of_walk (rc := rc) TfibB)
      (fun fw => FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst (fx := fw) (rc := rc) (SK := preset_sink_head))
      (fuzz_free_B rc)
      (fuzz_free_null_B rc)
      (H_text_pj_parse_B rc)
      (FuzzPickB.fuzz_pick_holds_B rc)
      (pj_write_B rc)
      (FCxmCfxB.stack_malloc1_contract_xm_cfx_B fz);
  pcc_read_members := fun fz =>
    read_members_Bp4.read_members_holds_Bp4 (fx := fz) (rc := rc) (RL := RLX) preset_sink_head;
  pcc_check_round_trip := H_text_check_round_trip_B rc;
  pcc_pj_free := pjf_B rc;
  pcc_fuzz_alloc_ran_out_reset := fun fz =>
    FuzzAllocAccInstB102.fuzz_alloc_ran_out_reset_holds_B_inst (fx := fz) (rc := rc) (SK := preset_sink_head);
  pcc_fuzz_alloc_most := fun fz =>
    FuzzAllocMostBp.fuzz_alloc_most_holds_B (fx := fz) (rc := rc) (SK := preset_sink_head) TfibB
      PwPstUnownedB.pst_unowned_TfibB;
  pcc_fuzz_alloc_live := fun fz => PRW_AfnBridgeB.pcc102_fuzz_alloc_live_of_walk (rc := rc) TfibB fz;
  pcc_fuzz_alloc_count := fun fz => PRW_AfnBridgeB.pcc102_fuzz_alloc_count_of_walk (rc := rc) TfibB fz;
  pcc_fuzz_alloc_peak_reset := fun fz =>
    PRW_AfnBridgeB.pcc102_fuzz_alloc_peak_reset_of_walk (rc := rc) TfibB PwPstUnownedB.pst_unowned_TfibB fz;
  pcc_fuzz_alloc_peak := fun fz => PRW_AfnBridgeB.pcc102_fuzz_alloc_peak_of_walk (rc := rc) TfibB fz;
  pcc_fuzz_alloc_ran_out := fun fz =>
    FuzzAllocAccInstB102.fuzz_alloc_ran_out_holds_B_inst (fx := fz) (rc := rc) (SK := preset_sink_head);
  pcc_stack_malloc := stack_malloc_B rc fy;
  pcc_stack_free := astack_free_law_ok_cf (rc := rc) (cp := CfParams_preset) tfibsegs TfibB |}.
Qed.

(* ---------------------------------------------------------------------- *)
(* C. THE B' PROGRAM SLOT at TfibB': the B' seam Ent102SeamB.preset_lib_x_stmt_B_holds (the walk of
   LLVMFuzzerTestOneInput, Ent102TopB.entry_B_walk) at the record above, at every float state; the slot the export
   takes, preset_lib_contract_x_all, is the seam's conclusion form (preset_lib_contract_xR at the re-hiding relation
   YA0nH.wle' segs RZ_cf, PresetCfnB.v) *)
Theorem preset_lib_contract_x_all_B : forall rc : YM05.RunCeil,
  preset_lib_contract_x_all (rc := rc)
    (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape)
    (L := B_prog_listing) (PA := PAB rc) (ci := CfImg_B)
    SMB NPB TfibB ameter_triv XLIB0 XLIB0 PRT.
Proof.
intros rc fx. exact (Ent102SeamB.preset_lib_x_stmt_B_holds rc fx XLIB0 XLIB0 PRT (pcc_all_B rc)).
Qed.

(* ---------------------------------------------------------------------- *)
(* D. The other Section hypotheses of the export (PresetD2pBPf.v Section closed), same text: the read
   interceptor's check. (malloc / free are in section B; memcpy / memset are aintrin_cpy_B / aintrin_set_B.) *)
(* OWNER: two Theorem Labs work streams, no result yet *)
Hypothesis H_aread_check_stmt_cf_B : forall rc : YM05.RunCeil, aread_check_stmt_cf (cp := CfParams_preset) TfibB.

(* ---------------------------------------------------------------------- *)
(* E. The room's decision and the no-room arm, at PAYLOAD_ROOM := fun _ => True. *)
Lemma PAYLOAD_ROOM_dec_B : PresetDrvTopBStmt.PAYLOAD_ROOM_dec_stmt PRT.
Proof. intros d. left. exact I. Qed.
Lemma payload_refusal_B : forall sp brk mbase rnd inp a0 p data, valid_sp sp -> valid_brk presetsegsAU brk ->
  valid_mmap_base mbase -> entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp -> in_argv inp = [a0; p]
  -> Fs.fs_lookup (in_fs inp) p = Some data -> ~ PRT (payload data) -> exists T, srealizes presetsegsAU
  (init_config presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp) T /\
  shape_ok Exits.ok_or_refused T.
Proof.
intros sp brk mbase rnd inp a0 p data Hsp Hbrk Hmb Hfit Hinp Hargv Hlook HNPR.
destruct (HNPR I).
Qed.

(* ---------------------------------------------------------------------- *)
(* F. The ASan side of the halts top, and the top. *)
Lemma TFIB_T_AU_H_closed_B : TFIB_T_AU_H.
Proof.
intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp.
(* the room arm: SPECX from the export at the slot of section C, exits 0 / 2 from HaltsTFIB.v's exit lemma *)
assert (ROOM : (forall a0 p data : list byte, in_argv inp = [a0; p] -> Fs.fs_lookup (in_fs inp) p = Some data ->
    PRT (payload data)) ->
  exists T, srealizes presetsegsAU
    (init_config presetsegsAU AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp) T /\
    shape_ok Exits.ok_or_refused T).
{ intros HROOM. exists (SPECX (LS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.ZTraceSpec.checksum_shape) inp).
  split; [| exact (presetAU_SPECX_shape_ok inp)].
  exact (PresetD2pBPf.TFIB_T_room_all_B_closed_stmt_holds
    H_amalloc_realizes_cf_keep_B H_afree_realizes_cf_B aintrin_cpy_B aintrin_set_B
    H_aread_check_stmt_cf_B
    SMB XLIB0 XLIB0 PRT preset_lib_contract_x_all_B
    sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hinp HROOM). }
(* argv's shape: only [a0; p] can ask for room (destruct also rewrites in_argv inp inside ROOM) *)
destruct (in_argv inp) as [| a0 [| p [| a2 rest]]] eqn:Hargv;
  [ apply ROOM; intros a0' p' data' Hargv'; discriminate Hargv'
  | apply ROOM; intros a0' p' data' Hargv'; discriminate Hargv'
  |
  | apply ROOM; intros a0' p' data' Hargv'; discriminate Hargv' ].
(* the file system's lookup of p: only a present file can ask for room *)
destruct (Fs.fs_lookup (in_fs inp) p) as [data |] eqn:Hlook.
2: { apply ROOM; intros a0' p' data' Hargv' Hlook'. injection Hargv' as _ Hp. subst p'.
     rewrite Hlook in Hlook'. discriminate Hlook'. }
(* argv = [a0; p], p holds data: the room decides the arm *)
destruct (PAYLOAD_ROOM_dec_B (payload data)) as [HPR | HNPR].
- apply ROOM; intros a0' p' data' Hargv' Hlook'. injection Hargv' as _ Hp. subst p'.
  rewrite Hlook in Hlook'. injection Hlook' as Hd. subst data'. exact HPR.
- (* destruct put [a0; p] for in_argv inp in Hfit too; payload_refusal_B takes it in its stated form *)
  rewrite <- Hargv in Hfit.
  exact (payload_refusal_B sp brk mbase rnd inp a0 p data Hsp Hbrk Hmb Hfit Hinp Hargv Hlook HNPR).
Qed.

Print Assumptions TFIB_T_AU_H_closed_B.

Theorem preset_asan_ubsan_halts_closed : Statements.asan_ubsan_halts.
Proof. exact (preset_asan_ubsan_halts_of_tfib TFIB_T_AU_H_closed_B). Qed.

Print Assumptions preset_asan_ubsan_halts_closed.
End closed.

(* the elaborated statements: the Section names are now the binders (implicit arguments shown, notations off) *)
Set Printing Implicit. Unset Printing Notations.
About pcc_check_reject_clean_B.
About pcc_all_B.
About preset_lib_contract_x_all_B.
About TFIB_T_AU_H_closed_B.
Check preset_asan_ubsan_halts_closed.
Print Assumptions preset_asan_ubsan_halts_closed.
(* the cited results alone *)
Print Assumptions bcmp_B.
Print Assumptions asan_memset_iface_B.
Print Assumptions asan_memcpy_iface_B.
Print Assumptions FuzzPickB.fuzz_pick_holds_B.
Print Assumptions Padded102B_Inst.padded_B_at_PI_prog_B.
Print Assumptions aunpoison_B.
Print Assumptions apoison_B.
Print Assumptions own_B.
Print Assumptions fuzz_malloc_B.
Print Assumptions OwnB_p102.own_holds_B.
Print Assumptions FuzzMallocB_p102_holds.fuzz_malloc_holds_B.
Print Assumptions fuzz_realloc_B.
Print Assumptions FuzzReallocB_p102.fuzz_realloc_holds_B'.
Print Assumptions fuzz_free_B.
Print Assumptions put_B.
Print Assumptions snprintf_B.
Print Assumptions put_string_B.
Print Assumptions write_value_B.
Print Assumptions pj_write_B.
Print Assumptions aintrin_cpy_B.
Print Assumptions aintrin_set_B.
Print Assumptions stack_malloc_B.
Print Assumptions Ent102SeamB.preset_lib_x_stmt_B_holds.
Print Assumptions preset_asan_ubsan_halts_of_tfib.
About PresetD2pBPf.TFIB_T_room_all_B_closed_stmt_holds.
Locate preset_asan_ubsan_halts_closed.
Print OSSVerify.omx_clap_core.fuzz_preset.Statements.asan_ubsan_halts.
Unset Printing Implicit. Set Printing Notations.
