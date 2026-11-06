(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 967 of its 1043 lines of code are new or changed and 1914 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/Cno102B_Base.v, with its module paths and module names changed; 336 of its 376 lines of code are new or changed and 1003 lines of the source are left out. *)
(* fuzz_preset lib/A, the #102 re-walk of tx_put on image A' (ASan build): the SHARED BASE of the segment lemmas
   of the walk. STATEMENTS ONLY: the entry record, the text's premises, the cut predicates and the
   segment statements; the segment files TxPut102A_S*.v prove them, TxPut102A_Top.v composes them and
   TxPut102A_Inst.v instantiates the image.
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   THE IMAGE: A' = asan pin sha256 1be0f53d96cb9d6c (unstripped twin bff8519bbe3ea0e4; 0 differing instruction words
   over the function range, the internal file REWALK-102-PLAN.md section 0).
   THE INPUTS, each BY PATH, cited by blob:
   - listing (owner 13:10Z): lib/A/Listing_prog.v
     1ab147923c5d, lib/A/PAImg_prog.v 47eeb54e93be, lib/Reusable/YPsym.v b6f5a85d234d. This file is PARAMETRIC over
     {PA : PAImg A_prog_listing} and uses the listing's own tables (PL_txp_A below, the terms of PAImg_prog.v
     :177-181), as Caw102A_Base.v does, so no file that checks the image's bytes is Required here.
   - the kit's text: the #102 KIT preset-tree-at-2026-10-29T17-47-10Z.tsv (sha256 9d6fcfaf6b8e; internal record) (announced, owner 18:08Z /
     18:10Z), lib/A/PRH_FnTx.v c3fc79dd52d9 (as first written; this tree's text has the budgeted fpostWbmR post, :341-343 here, and a dead REFUSED outcome, :328-330) (ttx_put_specX, PRH_FnTx.v:414 on this tree, :313-348 in that blob; the #102 struct text: failed at t + 24, 28 accessed
     bytes, ONE fpostWm with the three outcomes DONE / FAILED AT ENTRY / REFUSED, the GROW run event as a guarded entry
     premise, g_most and g_own_ran_out inside prh_ledger after the kit's ledger-field sweep), with PRH_Base.v
     (sha256 d27268feabfe; internal record) and PRH_Img.v (sha256 31cd90ba56d5; internal record) of the same tree. Earlier texts this walk proved: PRH_FnTx.v (sha256 b9cc6fd3c406; internal record),
     PRH_FnTx.v (sha256 00de73011bd4; internal record); prepared on PRH_FnTx.v (sha256 6218a889d82c; internal record).
   - engine set (owner 17:07Z): ALL 28 engine files by path from the lib/Reusable tree of preset-tree-at-2026-10-29T16-15-23Z.tsv (sha256 0e6c79df3746; internal record).
   - base: the #102-pins route, the fuzz_preset tree preset-tree-at-2026-10-29T13-32-27Z.tsv (sha256 da78a2d06acb; internal record) (= core, the fuzz_preset tree preset-tree-at-2026-10-29T11-03-54Z.tsv (sha256 5eec7fc06474; internal record) + listings preset-tree-at-2026-10-29T13-01-12Z.tsv (sha256 708a846af38f; internal record)
     + the three proof.yaml of facts preset-tree-at-2026-10-29T12-03-17Z.tsv (sha256 43b6000a63b5; internal record) + the kit's Batch 1 + the engine set).
   THE CODE (A' 0x84cec, 134 instructions, frame 112, 13 saved registers; DERIVED byte offsets from the entry, which
   is the listing's slot A_prog_slot AS_tx_put = 3523, never a typed address):
     +0    prologue: frame 112; ra +104, s0 +96, s1 +88, s2 +80, s3 +72, s4 +64, s5 +56, s6 +48, s7 +40, s8 +32,
           s9 +24, s10 +16, s11 +8; s1 = n, s6 = the shadow base (the GOT word A_OBJ 0 -> the cell A_OBJ 12),
           s0 = t, s4 = t + 24, s8 = shadow (t + 24), s2 = s; the 4-byte load check of t + 24 (slow path +420,
           REFUTED) and `lw a0, 0(s4)` = failed                                              [S0]
     +104  bnez a0 -> +332 (A0 FAILED AT ENTRY)
     +108  s3 = t + 8, s7 = shadow (t + 8), load check (report +472 REFUTED); s5 = t + 16, s9 = shadow (t + 16),
           load check (report +480 REFUTED); a0 = t->n, a2 = t->cap, a0 = n + len0, a1 = a0 + 1, s10 = t >> 3
     +168  bgeu a2, a1 -> +248 (A1 FIT); else fall into the grow block                        [S0 ends at both cuts]
     +172  TP_PC_GROW: s11 = shadow (t), load check of t (report +504 REFUTED); a0 = t->b, a1 = 2 * a1;
           jal __wrap_realloc (+192); beqz a0 -> +392 (A3 GROW-NULL)                          [S_GROW]
     +200  store check of t (report +528 REFUTED), `sd a0, 0(s0)`; load checks of t + 8 / t + 16 (+520 / +528
           REFUTED); a0 = (t->n + n) * 2 + 2; `sd a0, 0(s5)` = t->cap                         [S_GROW ends at FIT]
     +248  TP_PC_FIT: s10 = shadow (t), load check of t (report +488 REFUTED); load check of t + 8 (+496 REFUTED);
           a0 = t->b + t->n, a1 = s, a2 = n; jal __asan_memcpy (+288); t->n := t->n + n (`sd a0, 8(s0)`);
           the 1-byte store check of b + n' (slow path +440, REFUTED) and `sb zero, 0(a0)`    [S_FIT]
     +332  TP_PC_END: the 13 restores, `addi sp, sp, 112`, ret (+388)                         [S_END]
     +392  TP_PC_NULL: `sb 1` to g_own_ran_out (A_OBJ 13, no ASan check), the 4-byte store check of t + 24
           (slow path +452..+468, REFUTED), `sw 1, 0(s4)` = t->failed, j +332   [no segment: never reached, :513-515]
   THE FORM (the #102 continuation form, as Caw102A_Base.v): GENERIC P, abstract in every proof:
   `forall P, srr_inv_laws segs P -> [srr_inv_call segs P ->] tp_seg_* P`, each ending in
   SRr' segs RZ_cf W c (tp_QP P Q) with a generic final post Q; every segment but the last takes, for each cut it reaches,
   the continuation at that cut. The last (S_END) ends in fpostWbR .. (the text's post body). The top composes them and
   instantiates P := tp_mn D (the memnorm keep from the entry memory), which pays fpostWbmR's memnorm conjunct.
   THE ALLOCATOR: the cf instance, ARcfx := ARcf segs B /\ xs_placed_cf (FuzzFree.v / FuzzStrdup.v / Caw102A_Base.v's
   choice), room_live_cf at the instance prh_room_live_a8.
   NAMED ARGUMENTS (Section hypotheses of the segment files, owners in brackets):
   - the two of them are PREMISES of the twin text (tp_pre's), not segment arguments: TP_ROOM_EVENT, the
     model run's event at the entry position rp_i is the grow's own
     realloc / malloc. PRH_FnTx.v's text has no such premise, and the post's position conjunct
     `exists rp_i' rp_hist', rp_i <= rp_i' /\ iface_room_pos .. rp_i' .. S'` is NOT derivable without it on the
     GROW-OK arm: the only keep rules are PresetRoomPosKeep.room_pos_keep_realloc (:380) and
     room_pos_keep_realloc0 (:456), each of which asks for the event. Reported at 14:1xZ and
     ruled at 14:2xZ: carry it as ONE named argument of the GROW-OK arm, keep its use in ONE lemma, the texts' author restates the
     text as an implication keyed on the call's own run event. The FAILED, FIT and REFUSED arms need nothing
     (room_pos_keep_realloc_null / room_pos_keep_realloc0_null keep rp_i).
   - the callee TEXTS, verbatim: AREAL_cf (YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep, the primed row with the
     memnorm keep: the entry room and hull admission, amreal' segs RZ_cf, since realloc(p, n) frees the old block),
     AREAL_NULL_cf (YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep), AI (YGcallMxmn.aintrin_realizes_xm at
     OCpy).
   - PAL (PALib) and tp_img [the image instance]: image facts, proved at the instance by vm_compute.
   Numerals: the byte offsets 0..532 are DERIVED (4 x slot inside the function); 112 / 104 / 96 / 88 / 80 / 72 / 64 /
   56 / 48 / 40 / 32 / 24 / 16 / 8 are LENGTHs (the frame and its slots, read off `addi sp, sp, -112` and the sd
   immediates); 0 / 8 / 16 / 24 / 28 / 32 are LENGTHs (struct text's fields, its 28 accessed bytes and its size);
   register numbers 1 2 3 4 8 9 10 11 12 18..27 (WORD); 1 (WORD: the value stored in failed and g_own_ran_out);
   2 ^ 28 / 2 ^ 64 the text's bounds; 4096 (LENGTH: page). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallcf YGcallRx YGcallRcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRealloc ReallocP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YImgTop YGcfAmx2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require
  YGcfRehidePost YGcfInstReallocKKeep YGcfReallocComposeKeep YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the function's cut offsets (DERIVED byte offsets inside tx_put, A' listing 1ab147923c5d) ---- *)
Definition TP_SLOT : nat := 3523.
Definition TP_OFF : Z := 4 * Z.of_nat TP_SLOT.
Definition TP_FRAME : Z := 112.
Definition TP_PC_GROW : Z := 172.   (* the grow block: the load check of t, then the realloc call *)
Definition TP_PC_FIT : Z := 248.    (* the rejoin: the memcpy, the length update and the NUL store *)
Definition TP_PC_END : Z := 332.    (* the epilogue *)
Definition TP_PC_NULL : Z := 392.   (* the refused grow: g_own_ran_out := 1, failed := 1, j END *)
Lemma TP_OFF_val : TP_OFF = 14092.
Proof. vm_compute. reflexivity. Qed.
Lemma TP_FRAME_val : pi_frame (PrhImg := prh_img_A) F_tx_put = TP_FRAME.
Proof. vm_compute. reflexivity. Qed.

(* the listing's own tables (PAImg_prog.v 47eeb54e93be :177-181, the same terms; Required from no file that checks
   the #102 image's bytes): the engine's vm_compute needs a closed table, so the walk's PL is PL_txp_A *)
(* the tree is EVALUATED once here (a measurement on the B' twin, 15:5xZ: an
   unevaluated `ptree_of_list` is re-built by every vm_compute lookup of the engine - ten lookups took 918 s and
   146 GB); pl_tpi_eq is then a separate lemma, since an ltac inside the record cannot see L *)
Definition A_prog_tpi_txp : ptree asym := Eval vm_compute in (ptree_of_list A_prog_listing).
Lemma A_prog_tpi_txp_eq : ptree_of_list A_prog_listing = A_prog_tpi_txp.
Proof. vm_compute. reflexivity. Qed.
Definition A_prog_tw_txp : ctable := Eval vm_compute in (tw_of 0 A_prog_listing).
Definition PL_txp_A : PAListing A_prog_listing :=
{| pl_tpi := A_prog_tpi_txp; pl_tpi_eq := A_prog_tpi_txp_eq; pl_tw := A_prog_tw_txp; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.

Section tp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg A_prog_listing}.
(* the image's generated per-function data (PRH_Img.v, #102 pins), the listing's tables, and the room instance prh_room_live_a8,
   bound ONCE here *)
#[local] Instance TP_PrhImg : PrhImg := prh_img_A.
#[local] Instance TP_PAListing : PAListing A_prog_listing := PL_txp_A.
#[local] Instance TP_RL : PrhRoomLive := prh_room_live_a8.
#[local] Notation segs := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* (the batch kit's text dropped DW: prh_univ_closure takes CTX0 alone) *)
(* the allocator relation of the walk (YGcallcf.v's): ARcf with the error-buffer extents placed *)
Definition ARcfx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S.

(* ---- THE IMAGE FACTS the walk reads of PA, each proved at the instance by computation (PAImg_prog.v's
   A_entry_tx_put and A_prog_val, and the re-emitted object pin 13 = g_own_ran_out) ---- *)
Record tp_img : Prop := {
  tpi_base : BASE = A_prog_base;
  tpi_entry : SIGMA AS_tx_put = BASE + TP_OFF;
  tpi_realloc : SIGMA AS___wrap_realloc = cf_pc_wrap_realloc;
  (* NO field for __asan_memcpy: its text is taken at the listing's own `SIGMA AS___asan_memcpy`, as
     FuzzStrdup.v does, so no equation against `pc_asan_memcpy (as_code B)` is needed and
     tp_img stays a record of PA / CfImg facts, each closed at the instance by vm_compute. *)
  (* THE IMAGE BINDING OF B, in one field (YC1fP.v:322-330 PALibCore, the facts pinned at EVERY listing):
     as_got_shadow B = VAL (A_OBJ 0) and as_shadow_cell B = VAL (A_OBJ 12) - without them the prologue's GOT pair
     (A' 0x84d28 PHi 58 / 0x84d2c PLdHi .. (A_OBJ 0) .. SZ8, then 0x84d30 `ld s6, 0(a2)`) cannot use ARx's const
     law and s6 = SHADOW_OFF is unreachable, so tp_shregs and every shadow check are blocked (found at
     TPA-S0 / TPA-FIT, 15:1xZ); their disjointness palc_got_cell, which the entry state's region list needs; and
     api_env B (palc_env), which YGcallRx's realloc rule takes as errno_low. It is a fact of the BINDING of B, so
     the instance takes it from the unit's stand-in (FuzzFree.v:387 PAL's shape), not by computation.
     AUDIT of every image-dependent read of tx_put on A' (listing Listing_prog.v (sha256 62db5cdc9519; internal record), slots 3523..3656), so no
     further gap appears: slot 3539 is a TYPED PLdHi .. (A_OBJ 0) .. SZ8 (the GOT word: the listing names the
     object, only the two PALibCore equations are needed); slot 3540 `ld s6, 0(a2)` reads the shadow cell at the
     address that word holds (as_shadow_cell); slot 3621 PHi 59 + slot 3623 `sb a0, 1740(a1)` is the ONLY
     auipc-plus-immediate pair, and tpi_hi_own is its alias row; the realloc call needs tpi_realloc, the memcpy
     call is taken at SIGMA AS___asan_memcpy; the nine __asan_report_* calls are refuted, so they bind nothing. *)
  tpi_pal : PALibCore (PI := PA) B;
  tpi_own : VAL (A_OBJ 13) = pi_g_own_ran_out;
  (* the `sb 1` to g_own_ran_out is an auipc / store pair, so the walk needs the listing's ALIAS row: the high part
     A_HI 59 plus the store's immediate 1740 is the object's address (A' 0x84e74-0x84e7c; the alias is proved at the
     instance, PAImg_prog.v's A_prog_val, in Cno102A_Base.v cni_hi9's shape). A finding (TPA-NULL,
     15:0xZ): without it tp_seg_NULL (since removed: the NULL cut is never reached) was not provable. *)
  tpi_hi_own : VAL (A_HI 59) + 1740 = VAL (A_OBJ 13);
  (* the program-written statics are writable image bytes, outside the read-only view (two findings of the Caw102A_*.v walk: the
     journal exempts prh_pst from its image clause, and the runtime rules keep a static only when in_img) *)
  tpi_pst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a;
  tpi_pst_img : forall a, Exists (in_zr a) prh_pst -> in_img segs a;
  (* the two B-side facts the PST write rule asks (YCbqG.v:575 ajournal_x_pst_write): a static of prh_pst is not one
     of the runtime's own statics and is not errno. They are facts of the IMAGE BINDING of B, not of PA, so the
     instance file does not close them by computation: it takes them from the unit's binding of B, as FuzzFree.v
     :389-390 (pal_pst_ok) and Cno102A_Base.v (cni_pst_ok) do. Owner: the kit. A finding (TPA-NULL). *)
  tpi_pst_owned : forall a, Exists (in_zr a) prh_pst -> ~ Exists (in_zr a) (as_owned_static B);
  tpi_pst_errno : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4);
  (* The GROW row's two findings (15:4xZ), both from tp_side after the realloc - GROW is the only row that carries
     src_rd and the ledger across an allocator call:
     - the harness head is at least one shadow granule wide (PRH_Base.v's prh_head_wide, the spelling every walk
       takes): prh_hblock reads 8 head bytes at a - cf_head and the call journal keeps only the bytes i < req_size
       (k + cf_head) of a live block, so under a generic CfParams a head narrower than 8 lies partly outside every
       kept block. A CfParams fact: cf_head = 16 at the instance, by vm_compute;
     - the image's shadow is present in every ARcf state (YGcfAmx2.img_shadow_vis_cf, "which the unit
       supplies", here over YImgTop's IMG_LO / IMG_TOP, the names kept_at and kept_img use): src_rd's
       shadow_hull_vis for an in_zs global or a kept_img string reads shadow bytes outside the zero-shadow ranges
       and the const cells, which neither ARcf nor a journal clause keeps across the realloc. A fact of the image
       binding of B: the instance takes img_shadow_vis_cf from the unit's stand-in (FuzzStrdup.v:249-251's
       shape) and bridges cf_img_lo / cf_img_top to IMG_LO / IMG_TOP by vm_compute. *)
  tpi_head_wide : prh_head_wide;
  (* over the instance's own image bounds pa_lo / pa_hi, the wording of kept_at / kept_img since PRH_Base.v
     (sha256 d27268feabfe; internal record) (the GROW row's finding 18:3xZ: the IMG_LO / IMG_TOP form no longer meets them) *)
  tpi_img_shvis : forall ly S Hp (W : world segs) mem md a, ARcf segs B ly S Hp W mem md ->
    @pa_lo _ _ PA <= a < @pa_hi _ _ PA -> aview segs (w_H W) mem (shadow_addr a) <> None;
  (* the allocator hull at a run position of a run of at most 4 calls, two CfParams facts the instance closes at
     preset's CfParams (lib/A/PresetHullPay.v hull_budget_of_room_pos + hull_ok_of_budget at the empty list; lib/A/
     PresetDrvHeadroomA.v drv_cf_headroom_at_call_A): the admission at the call (QM_cf_of_room, the realloc rule's
     QMm) and the realloc tree's entry headroom (the primed row's cf_hull_adm) *)
  tpi_hull_ok : forall sm x os i H0 hist S, (length os <= 4)%nat -> PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    cf_hull_ok S;
  tpi_hull_adm : forall sm x os i H0 hist S m n, (length os <= 4)%nat ->
    PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HRe m n) -> cf_hull_adm S n;
  (* the cf layer's read-only bounds at the listing's (YGcallcf.arodata_ok_cf_of_journal_P's premises): the call
     memory's arodata_ok_cf, which the realloc rule's QMm_cf asks, from the carry's arodata_okP and the journal *)
  tpi_relro_seg : relro_seg_t segs;
  tpi_errno_relro : errno_relro_t B;
  tpi_relro_bounds : @pa_relro_lo _ _ PA = cf_relro_lo /\ @pa_relro_hi _ _ PA = cf_relro_hi /\ cf_relro_hi <= 2 ^ 64;
  tpi_relro_pst : forall a, aro_addr_cf a -> ~ Exists (in_zr a) prh_pst;
  tpi_ro_reads_nw : YGcfAroBridge.ro_reads_nw_t segs
}.

Definition tp_pc (o : Z) : Z := BASE + TP_OFF + o.

(* ---- THE ENTRY DATA: every binder of ttx_put_specX (PRH_FnTx.v c3fc79dd52d9 :314-317), in the text's order ---- *)
Record tp_in : Type := mkTpIn {
  tp_rp_sm : list Z -> Z * Z; tp_rp_x : list Z; tp_rp_os : list (option nat * option nat * option nat);
  tp_rp_i : nat; tp_rp_H0 : list Z; tp_rp_hist : list YG00.chunk;
  tp_ly : alayout; tp_S : astate; tp_Hp : list Z; tp_W : world segs;
  tp_regs : bvmap 5 word; tp_mem : word -> option byte; tp_md : Model; tp_ch : list (Z * Z * Z);
  tp_dw : Z; tp_t : Z; tp_s : Z; tp_n : Z; tp_b0 : Z; tp_len0 : Z; tp_cap0 : Z; tp_f0 : Z; tp_own : Z;
  tp_txt : list Z; tp_src : list Z; tp_Lam : list (Z * Z);
  tp_peak : Z; tp_cnt : Z; tp_fail : Z; tp_ran : Z; tp_most : Z
}.
Definition tp_sp0 (D : tp_in) : Z := spZ (tp_regs D).
(* the grow's request: 2 * (len0 + n + 1), and the capacity the DONE arm gives (TxModel.tx_cap1) *)
Definition tp_need (D : tp_in) : Z := tp_len0 D + tp_n D + 1.
Definition tp_req (D : tp_in) : Z := 2 * tp_need D.
Definition tp_cap1 (D : tp_in) : Z := TxModel.tx_cap1 (tp_len0 D) (tp_cap0 D) (tp_n D).
(* the number of this call's run events (prhtx_evs: one per grow), the batch-kit text's wild-room and consumer-window count *)
Definition tp_evk (D : tp_in) : nat := length (prhtx_evs (tp_len0 D) (tp_cap0 D) [tp_n D]).
Lemma tp_evk_grow : forall D, tp_cap0 D < tp_need D -> tp_evk D = 1%nat.
Proof.
intros D H. unfold tp_evk, tp_need in *. cbn [prhtx_evs].
destruct (tp_len0 D + tp_n D + 1 <=? tp_cap0 D) eqn:E; [apply Z.leb_le in E; lia | reflexivity].
Qed.
Lemma tp_evk_fit : forall D, tp_need D <= tp_cap0 D -> tp_evk D = 0%nat.
Proof.
intros D H. unfold tp_evk, tp_need in *. cbn [prhtx_evs].
destruct (tp_len0 D + tp_n D + 1 <=? tp_cap0 D) eqn:E; [reflexivity | apply Z.leb_gt in E; lia].
Qed.

(* ---- ttx_put_specX_ev's premises (lib/A/Prog/TxPutCall102.v, the shared twin of the kit's ttx_put_specX, with tp_live
   after the iface_room_pos premise) but the kit text's two new premises (tp_k1pre below), at one record, in the twin's order, and
   the run-length premise (length rp_os <= 4) LAST, so the positional reads of the earlier conjuncts do not move ---- *)
Definition tp_pre (D : tp_in) : Prop :=
  fpre B ARcfx STK_tx_put (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_regs D) (tp_mem D) (tp_md D) (tp_ch D) /\
  prh_univ_closure B CTX0 /\
  room_live_cf (tp_S D) /\
  PresetRoomPos.iface_room_pos (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_rp_H0 D) (tp_rp_hist D) (tp_S D) /\
  TxPutCall102.tp_live (tp_S D) /\
  (* The texts' author took the run event into the text (at PRH_FnTx.v (sha256 00de73011bd4; internal record) as the position conjunct's hypothesis, at
     PRH_FnTx.v (sha256 6218a889d82c; internal record) as the guarded entry premise below), so the twin inserts tp_live alone *)
  getr (tp_regs D) 10 = w64 (tp_t D) /\ getr (tp_regs D) 11 = w64 (tp_s D) /\ getr (tp_regs D) 12 = w64 (tp_n D) /\
  fwin (tp_ly D) (tp_W D) (tp_regs D) (tp_mem D) (tp_dw D) /\
  prhtx_place (tp_ly D) (tp_S D) (tp_W D) (tp_regs D) (tp_mem D) (tp_dw D) (tp_t D) /\
  prhtx_trace B (tp_ly D) (tp_W D) (tp_mem D) (tp_t D) /\
  prhtx_rec (tp_W D) (tp_mem D) (tp_t D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_f0 D) /\
  prhtx_inv B (tp_Lam D) (tp_ly D) (tp_S D) (tp_W D) (tp_mem D) (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_txt D) /\
  src_rd (tp_W D) (tp_mem D) (tp_s D) (tp_src D) /\ Z.of_nat (length (tp_src D)) = tp_n D /\
  prhtx_kept B (tp_Lam D) (tp_ly D) (tp_S D) (tp_s D) (tp_n D) /\
  (forall a, tp_s D <= a < tp_s D + tp_n D ->
     ~ (tp_t D <= a < tp_t D + 28) /\ ~ (tp_b0 D <= a < tp_b0 D + tp_cap0 D)) /\
  tp_need D <= 2 ^ 28 /\
  prh_ledger B (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_Lam D)
    (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) (tp_own D) /\
  (* the GROW event, the entry premise verbatim (PRH_FnTx.v c3fc79dd52d9; guarded by f0 = 0) *)
  (tp_f0 D = 0 -> tp_cap0 D < tp_len0 D + tp_n D + 1 ->
     nth_error (PresetRun.hruns (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D)) (tp_rp_i D) =
       Some (if tp_cap0 D =? 0 then PresetReqAt.HMal (2 * (tp_len0 D + tp_n D + 1))
             else PresetReqAt.HRe (tp_cap0 D) (2 * (tp_len0 D + tp_n D + 1)))) /\
  blocks_bytes (tp_S D) - tp_cap0 D + LIVE_tx <= LIVE_MAX /\ tp_req D < cf_malloc_max /\
  (length (tp_rp_os D) <= 4)%nat.
(* The batch-kit text's two new premises (PRH_FnTx.v 88468bf162d8 :412, :420), both GUARDED by f0 = 0 (TX-RUNAT-F0): the
   WILD ROOM for this call's own stored traces (one per grow), and the CONSUMER WINDOW over its own run events. Kept
   out of tp_pre so the rows' positional reads of tp_pre do not move; tp_text_of_walk puts them back in the text's
   order. *)
Definition tp_k1pre (D : tp_in) : Prop :=
  (tp_f0 D = 0 -> YCbqGwild.wild_room (as_universe B) [] (tp_evk D) (st_depot (tp_S D))) /\
  (tp_f0 D = 0 -> PRH_Base.prh_cons_from (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_evk D)).
(* The batch-kit post's wild-trace budget (PRH_Base.wbudget_if): at most tp_evk D fresh wild traces, when entered unfailed *)
Definition tp_budget (D : tp_in) (WS : list (list Z)) : Prop := wbudget_if (tp_f0 D) [] (tp_evk D) WS.
Lemma tp_budget_nil : forall D, tp_budget D [].
Proof. intros D _. unfold wbudget, wfresh, wild_fresh. cbn. apply Nat.le_0_l. Qed.

(* THE RUN POSITION, in the two shapes the post conjuncts have (PRH_FnTx.v c3fc79dd52d9; the same
   definitions as the B' walk's lib/B/Prog/TxPut102B_Base.v, so the two walks keep one shape): keyed on the
   outcome f1, so ONE pair covers the fit, the grow and the refused arm. tp_pos_grow is the position ADVANCED by
   this call's own grow (its run event is tp_pre's guarded entry premise, this walk's wording, which the texts' author took into
   the text); tp_pos_keep is the position UNMOVED, for every outcome that makes no event. *)
Definition tp_pos_grow (D : tp_in) (S' : astate) (f1 : Z) : Prop :=
  tp_f0 D = 0 -> f1 = 0 -> tp_cap0 D < tp_need D ->
  exists hist', PresetRoomPos.iface_room_pos (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D)
    (Datatypes.S (tp_rp_i D)) (tp_rp_H0 D) hist' S'.
Definition tp_pos_keep (D : tp_in) (S' : astate) (f1 : Z) : Prop :=
  ~ (tp_f0 D = 0 /\ f1 = 0 /\ tp_cap0 D < tp_need D) ->
  PresetRoomPos.iface_room_pos (tp_rp_sm D) (tp_rp_x D) (tp_rp_os D) (tp_rp_i D) (tp_rp_H0 D) (tp_rp_hist D) S'.
Definition tp_pos (D : tp_in) (S' : astate) (f1 : Z) : Prop :=
  tp_pos_grow D S' f1 /\ tp_pos_keep D S' f1.

(* ---- the text's post BODY (:331-350), with the regs' argument dropped: it does not occur in the text's body ---- *)
Definition tp_Q (D : tp_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (mem' : word -> option byte) : Prop :=
  exists b1 cap1 f1 own' (pre : list Z),
  prhtx_post B (tp_Lam D) (tp_regs D) (tp_dw D) (tp_ly D) (tp_S D) (tp_Hp D) ly' S' Hp' W' mem'
    (tp_t D) (tp_b0 D) (tp_cap0 D) b1 (tp_len0 D + Z.of_nat (length pre)) cap1 f1 (tp_txt D ++ pre) /\
  ((tp_f0 D = 0 /\ f1 = 0 /\ own' = tp_own D /\ pre = tp_src D /\ cap1 = tp_cap1 D) \/
   (tp_f0 D <> 0 /\ f1 = tp_f0 D /\ own' = tp_own D /\ pre = [] /\ b1 = tp_b0 D /\ cap1 = tp_cap0 D) \/
   (tp_f0 D = 0 /\ tp_cap0 D < tp_need D /\ f1 = 1 /\ own' = 1 /\ pre = [] /\ b1 = tp_b0 D /\ cap1 = tp_cap0 D /\
    prhtx_refused_at S' /\ rd32 (aview segs (w_H W') mem') (as_errno B) 12)) /\
  (* DEAD-TXPUT (the kit's text): entered unfailed, tx_put returns unfailed - the realloc's NULL is refuted at the
     call (PRH_Refute.prh_refute_tx_put), so the REFUSED arm, still stated, is never the one a walk gives *)
  (tp_f0 D = 0 -> f1 = 0) /\
  bytes_at W' mem' (tp_s D) (tp_src D) /\
  room_live_cf S' /\
  tp_pos_grow D S' f1 /\ tp_pos_keep D S' f1 /\
  prh_ledger B ly' S' Hp' W' mem' (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) own'.
Definition tp_Qb (D : tp_in) : alayout -> astate -> list Z -> world segs -> bvmap 5 word ->
  (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' _ mem' _ => tp_Q D ly' S' Hp' W' mem'.
Definition tp_cfg0 (D : tp_in) : config :=
  cfg_at segs (SIGMA AS_tx_put) (tp_regs D) (tp_mem D) (tp_md D).
Definition tp_text_post (D : tp_in) : world segs -> config -> Prop :=
  fpostWbmR B ARcfx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if (tp_f0 D) [] (tp_evk D)) STK_tx_put (tp_dw D)
    (prhtx_fp (tp_t D) (tp_b0 D) (tp_cap0 D)) (tp_regs D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) (tp_Qb D).
(* the END segment's post: the caller-window post at the text's budget, WITHOUT fQmn's memnorm conjunct (`memnorm
   mem -> memnorm mem'`), which is NOT provable at an abstract P (the END row's finding, 14:4xZ: every mem3 fact of
   tp_at_END reads mem3 through aview / mrestrict, and memnorm reads the raw overlay - YSRrMemnorm.v:1-2 says the same
   of a generic SRr), so the END row concludes fpostWbR and TxPut102A_Top.v adds the conjunct at P := tp_mn D, where
   `P (ms_mem (cfg_ms c'))` IS that implication. Both posts are at the text's relation wle' segs RZ_cf. *)
Definition tp_text_postW (D : tp_in) : world segs -> config -> Prop :=
  fpostWbR B ARcfx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if (tp_f0 D) [] (tp_evk D)) STK_tx_put (tp_dw D)
    (prhtx_fp (tp_t D) (tp_b0 D) (tp_cap0 D)) (tp_regs D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) (tp_Qb D).

(* THE RECORD IS THE TWIN TEXT: a walk of every record whose premises hold is TxPutCall102's ttx_put_specX_ev at
   ARcfx - the batch kit's ttx_put_specX verbatim with the one named premise tp_live (TxPutCall102.v's header). This lemma
   checks that tp_pre + tp_k1pre and tp_text_post are the twin's, binder for binder. *)
Lemma tp_text_of_walk :
  (forall D, tp_pre D -> tp_k1pre D -> SRr' segs YGcfRehidePost.RZ_cf (tp_W D) (tp_cfg0 D) (tp_text_post D)) ->
  TxPutCall102.ttx_put_specX_ev B ARcfx SK CTX0.
Proof.
intros HW rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src Lam
  peak cnt fail ran most H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25.
apply (HW (mkTpIn rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src
   Lam peak cnt fail ran most)).
- unfold tp_pre.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13|].
  split; [exact H14|]. split; [exact H15|]. split; [exact H16|]. split; [exact H17|]. split; [exact H18|].
  split; [exact H19|]. split; [exact H20|]. split; [exact H21|]. split; [exact H22|]. split; [exact H23|].
  split; [exact H24|]. split; [exact H25 | exact H6].
- split; [exact H7 | exact H8].
Qed.


(* ---- WHAT EVERY CUT CARRIES ---- *)
Definition tp_FP (D : tp_in) : list (Z * Z) := prhtx_fp (tp_t D) (tp_b0 D) (tp_cap0 D).
(* the widened journal from entry at the wild-trace budget WS (YCbqG.ajournal_xw; WS = [] is ajournal_x): window
   STK_tx_put + dw below sp0 + dw, FP the record and the old buffer. WS is [] up to the GROW's realloc and that call's
   wild trace after it (the batch kit: the trace is wild, inU, so the call's post keeps it in the budget) *)
Definition tp_J (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (mem3 : word -> option byte) (md3 : Model) (k : Z) (WS : list (list Z)) : Prop :=
  ajournal_xw (SK := SK) segs B prh_pst ARcfx (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem3 md3 k WS.
(* tp_J over a world relation R: a COPY of tp_J's body with the journal ajournal_xwR R (the walk's proofs unfold tp_J
   and read its body, so tp_J stays); tp_J_R_wle checks by reflexivity that tp_J is tp_JR at wle. After the GROW's
   realloc the journal from entry holds at the text's relation wle' segs RZ_cf. *)
Definition tp_JR (R : world segs -> world segs -> Prop) (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z)
  (W3 : world segs) (mem3 : word -> option byte) (md3 : Model) (k : Z) (WS : list (list Z)) : Prop :=
  ajournal_xwR (SK := SK) segs B prh_pst ARcfx R (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem3 md3 k WS.
Lemma tp_J_R_wle : forall D ly3 S3 Hp3 W3 mem3 md3 k WS,
  tp_J D ly3 S3 Hp3 W3 mem3 md3 k WS = tp_JR (@wle segs) D ly3 S3 Hp3 W3 mem3 md3 k WS.
Proof. reflexivity. Qed.
(* the walk's own keep relative to the entry state, over the window it may disturb: STK_tx_put below sp0 - its own
   frame 112 PLUS the stack a callee may use. The GROW row's finding (14:5xZ): with a window of 112 this predicate is
   FALSE at the FIT and NULL cuts, because after the realloc (+192) and the __asan_memcpy (+288) the callee scratch
   [sp0 - STK_tx_put, sp0 - 112) is not kept - realloc_leaf_x / acall_kept_x / aj_intrin_at_x all exempt it through
   ascratch / ESTACK - and cj_kept_trans cannot repair it (it asks sp1 - STK1 <= sp2 - STK2). STK_tx_put is also the
   window YCbqGcallW.fpostW_x_of_kept takes at the return, so END is unchanged. Written cells OR: the record's 28
   bytes and the old buffer, both in FP. *)
Definition tp_OR (D : tp_in) : list (Z * Z) := tp_FP D.
Definition tp_K (D : tp_in) (ly3 : alayout) (S3 : astate) (W3 : world segs) (mem3 : word -> option byte)
  (md3 : Model) : Prop :=
  cj_kept (SK := SK) segs B prh_pst STK_tx_put (tp_sp0 D) (tp_OR D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_W D) (tp_mem D) (tp_md D) ly3 S3 W3 mem3 md3.
(* tp_K over a world relation R (YCbqGcallW.cj_keptR; its world conjunct is wle in tp_K, which the realloc breaks) *)
Definition tp_KR (R : world segs -> world segs -> Prop) (D : tp_in) (ly3 : alayout) (S3 : astate) (W3 : world segs)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  cj_keptR (SK := SK) segs B prh_pst R STK_tx_put (tp_sp0 D) (tp_OR D) (tp_FP D)
    (tp_ly D) (tp_S D) (tp_W D) (tp_mem D) (tp_md D) ly3 S3 W3 mem3 md3.
Lemma tp_K_R_wle : forall D ly3 S3 W3 mem3 md3,
  tp_K D ly3 S3 W3 mem3 md3 = tp_KR (@wle segs) D ly3 S3 W3 mem3 md3.
Proof. reflexivity. Qed.
(* gp and tp, the only registers tx_put never writes and never restores *)
Definition tp_kregs (D : tp_in) (regs3 : bvmap 5 word) : Prop :=
  forall r : bv 5, In r [3; 4]%bv -> getr regs3 r = getr (tp_regs D) r.
(* the prologue's thirteen saved words, at sp0 - 8 .. sp0 - 104 *)
Definition tp_saved (D : tp_in) (W3 : world segs) (mem3 : word -> option byte) : Prop :=
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 8) 8 (raZ (tp_regs D)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 16) 8 (bv_unsigned (getr (tp_regs D) 8)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 24) 8 (bv_unsigned (getr (tp_regs D) 9)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 32) 8 (bv_unsigned (getr (tp_regs D) 18)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 40) 8 (bv_unsigned (getr (tp_regs D) 19)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 48) 8 (bv_unsigned (getr (tp_regs D) 20)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 56) 8 (bv_unsigned (getr (tp_regs D) 21)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 64) 8 (bv_unsigned (getr (tp_regs D) 22)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 72) 8 (bv_unsigned (getr (tp_regs D) 23)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 80) 8 (bv_unsigned (getr (tp_regs D) 24)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 88) 8 (bv_unsigned (getr (tp_regs D) 25)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 96) 8 (bv_unsigned (getr (tp_regs D) 26)) /\
  val_mem segs (rdW W3 mem3) (tp_sp0 D - 104) 8 (bv_unsigned (getr (tp_regs D) 27)).
(* the carry: the entry's premises, the journal and the keep from entry, the kept and saved registers, the frame
   pointer, Hp, and the read-only view (it rides through the journal's image clause) *)
Definition tp_carry (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) (WS : list (list Z)) : Prop :=
  tp_pre D /\ tp_J D ly3 S3 Hp3 W3 mem3 md3 k WS /\ tp_K D ly3 S3 W3 mem3 md3 /\ tp_kregs D regs3 /\
  spZ regs3 = tp_sp0 D - TP_FRAME /\ tp_saved D W3 mem3 /\ Hp3 = tp_Hp D /\
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W3) mem3).
(* tp_carry over a world relation R: its journal and keep at R (tp_carry is unfolded by the walks, so it stays) *)
Definition tp_carryR (R : world segs -> world segs -> Prop) (D : tp_in) (ly3 : alayout) (S3 : astate)
  (Hp3 : list Z) (W3 : world segs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z)
  (WS : list (list Z)) : Prop :=
  tp_pre D /\ tp_JR R D ly3 S3 Hp3 W3 mem3 md3 k WS /\ tp_KR R D ly3 S3 W3 mem3 md3 /\ tp_kregs D regs3 /\
  spZ regs3 = tp_sp0 D - TP_FRAME /\ tp_saved D W3 mem3 /\ Hp3 = tp_Hp D /\
  arodata_okP segs (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview segs (w_H W3) mem3).
Lemma tp_carry_R_wle : forall D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS,
  tp_carry D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS = tp_carryR (@wle segs) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS.
Proof. reflexivity. Qed.
(* the shadow registers the body keeps live: s6 = the shadow base, s0 = t and the three checked offsets *)
Definition tp_shregs (D : tp_in) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 22 = w64 SHADOW_OFF /\ getr regs3 8 = w64 (tp_t D) /\
  getr regs3 9 = w64 (tp_n D) /\ getr regs3 18 = w64 (tp_s D).
(* the state of the record and the buffer at a cut, with the buffer's capacity and base possibly moved *)
Definition tp_recat (D : tp_in) (W3 : world segs) (mem3 : word -> option byte) (b1 len1 cap1 f1 : Z) : Prop :=
  prhtx_rec W3 mem3 (tp_t D) b1 len1 cap1 f1.
(* the buffer's block facts WITHOUT its bytes (the bytes differ between the fit and the grow arm) *)
Definition tp_blk (D : tp_in) (ly3 : alayout) (S3 : astate) (W3 : world segs) (mem3 : word -> option byte)
  (b1 cap1 : Z) : Prop :=
  0 < cap1 /\ In (b1, cap1) (ablocks B ly3 S3) /\ 4096 <= b1 /\ b1 + cap1 + 8 <= YM05.alloc_ceiling /\
  amem_range b1 cap1 /\
  (forall a, b1 <= a < b1 + cap1 -> writable_at segs (rdW W3 mem3) a) /\
  range_addressable (aview segs (w_H W3) mem3) SHADOW_OFF b1 cap1 /\
  shadow_hull_vis (aview segs (w_H W3) mem3) b1 cap1 /\
  (forall a k, In (a, k) (tp_Lam D) -> a - cf_head <> b1).
(* what the ledger (with g_most and g_own_ran_out inside it since the kit's ledger-field sweep,
   preset-tree-at-2026-10-29T17-47-10Z.tsv (sha256 9d6fcfaf6b8e; internal record)), the source window and the room say at a cut
   (the run position is carried separately, by tp_pos at the cut's own outcome: the GROW cut has the entry's, which tp_pre already gives) *)
Definition tp_side (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (mem3 : word -> option byte) (own3 : Z) : Prop :=
  prh_ledger B ly3 S3 Hp3 W3 mem3 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D) (tp_most D) own3 /\
  src_rd W3 mem3 (tp_s D) (tp_src D) /\ room_live_cf S3.

(* ---- THE CUTS ---- *)
(* TP_PC_GROW (+172): failed was 0 and the buffer does not fit; a0 = t->b is not yet loaded, a1 = need, a2 = cap0;
   the state is the entry's but for tx_put's own frame; the journal is still at the empty budget; the batch-kit text's wild
   room and consumer window ride in front *)
Definition tp_at_GROW (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  tp_k1pre D /\ tp_carry D ly3 S3 Hp3 W3 regs3 mem3 md3 k [] /\ tp_shregs D regs3 /\
  tp_f0 D = 0 /\ tp_cap0 D < tp_need D /\
  ly3 = tp_ly D /\ S3 = tp_S D /\
  getr regs3 11 = w64 (tp_need D) /\ getr regs3 12 = w64 (tp_cap0 D) /\
  getr regs3 19 = w64 (tp_t D + 8) /\ getr regs3 21 = w64 (tp_t D + 16) /\ getr regs3 20 = w64 (tp_t D + 24) /\
  getr regs3 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8) /\ getr regs3 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8) /\
  getr regs3 24 = w64 (SHADOW_OFF + (tp_t D + 24) / 8) /\ getr regs3 26 = w64 (tp_t D / 8) /\
  tp_recat D W3 mem3 (tp_b0 D) (tp_len0 D) (tp_cap0 D) 0 /\
  prhtx_inv B (tp_Lam D) ly3 S3 W3 mem3 (tp_b0 D) (tp_len0 D) (tp_cap0 D) (tp_txt D) /\
  prhtx_trace B ly3 W3 mem3 (tp_t D) /\
  tp_side D ly3 S3 Hp3 W3 mem3 (tp_own D).
(* TP_PC_FIT (+248): the rejoin. The record holds (b1, len0, cap1, 0), the buffer holds txt in its first len0 bytes
   and has room for n + 1 more; the arm says whether the buffer moved (FIT: not; GROW-OK: the realloc's result); the
   journal is at some budget WS within the text's (the grow's wild trace, or none) *)
Definition tp_fitarm (D : tp_in) (ly3 : alayout) (S3 : astate) (b1 cap1 : Z) : Prop :=
  (tp_need D <= tp_cap0 D /\ b1 = tp_b0 D /\ cap1 = tp_cap0 D /\ ly3 = tp_ly D /\ S3 = tp_S D) \/
  (tp_cap0 D < tp_need D /\ cap1 = tp_req D /\
   prhtx_grow B (tp_ly D) (tp_S D) ly3 S3 (tp_b0 D) (tp_cap0 D) b1 cap1 /\
   blocks_bytes S3 <= blocks_bytes (tp_S D) + cap1 - tp_cap0 D).
Definition tp_at_FIT (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k b1 cap1 : Z) : Prop :=
  exists WS, tp_budget D WS /\
  tp_carryR (wle' segs YGcfRehidePost.RZ_cf) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS /\ tp_shregs D regs3 /\
  tp_f0 D = 0 /\
  getr regs3 19 = w64 (tp_t D + 8) /\ getr regs3 21 = w64 (tp_t D + 16) /\
  getr regs3 23 = w64 (SHADOW_OFF + (tp_t D + 8) / 8) /\ getr regs3 25 = w64 (SHADOW_OFF + (tp_t D + 16) / 8) /\
  getr regs3 26 = w64 (tp_t D / 8) /\
  tp_recat D W3 mem3 b1 (tp_len0 D) cap1 0 /\
  tp_blk D ly3 S3 W3 mem3 b1 cap1 /\ bytes_at W3 mem3 b1 (tp_txt D) /\
  tp_need D <= cap1 /\
  (forall a, tp_s D <= a < tp_s D + tp_n D -> ~ (b1 <= a < b1 + cap1)) /\
  prhtx_kept B (tp_Lam D) ly3 S3 (tp_s D) (tp_n D) /\
  tp_fitarm D ly3 S3 b1 cap1 /\
  tp_side D ly3 S3 Hp3 W3 mem3 (tp_own D) /\ tp_pos D S3 0.
(* TP_PC_END (+332): the text's post body already holds at this state; the epilogue only restores and returns. (The
   batch kit's text has NO refused path: the GROW row refutes the realloc's NULL, PRH_Refute.prh_refute_tx_put, so the NULL cut
   +392 is never reached and has no segment.) *)
Definition tp_at_END (D : tp_in) (ly3 : alayout) (S3 : astate) (Hp3 : list Z) (W3 : world segs)
  (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) (k : Z) : Prop :=
  exists WS, tp_budget D WS /\
  tp_carryR (wle' segs YGcfRehidePost.RZ_cf) D ly3 S3 Hp3 W3 regs3 mem3 md3 k WS /\ tp_Q D ly3 S3 Hp3 W3 mem3.

(* the machine configuration at a cut of the function *)
Definition tp_cfg (o : Z) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : config :=
  mkCfg (YK11.mkst regs3 (Z_to_bv 64 (tp_pc o)) mem3 (YK11.seg_rom segs)) md3.
(* a segment's post: the final post Q, and the invariant P at the end memory *)
Definition tp_QP (P : (word -> option byte) -> Prop) (Q : world segs -> config -> Prop) : world segs -> config -> Prop :=
  fun W' c' => Q W' c' /\ P (ms_mem (cfg_ms c')).

(* ---- THE SEGMENT STATEMENTS (generic P, generic final post Q; continuation form). After the move the walk ends at
   the text's relation: every statement concludes SRr' segs RZ_cf, and the post-call cuts FIT / END carry the journal
   at wle' segs RZ_cf. The GROW continuation is generic in the relation (tp_k_GROWR; tp_k_GROW is it at wle). ---- *)
Section segs. Variable P : (word -> option byte) -> Prop.
Definition tp_k_GROWR (R : world segs -> world segs -> Prop) (Q : world segs -> config -> Prop) (D : tp_in) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k,
    tp_at_GROW D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
    SRrG segs R W3 (tp_cfg TP_PC_GROW regs3 mem3 md3) (tp_QP P Q).
Definition tp_k_GROW (Q : world segs -> config -> Prop) (D : tp_in) : Prop := tp_k_GROWR (@wle segs) Q D.
Lemma tp_k_GROW_R_wle : forall Q D, tp_k_GROW Q D = tp_k_GROWR (@wle segs) Q D.
Proof. reflexivity. Qed.
Definition tp_k_FIT (Q : world segs -> config -> Prop) (D : tp_in) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1,
    tp_at_FIT D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 -> P mem3 ->
    SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_FIT regs3 mem3 md3) (tp_QP P Q).
Definition tp_k_END (Q : world segs -> config -> Prop) (D : tp_in) : Prop :=
  forall ly3 S3 Hp3 W3 regs3 mem3 md3 k,
    tp_at_END D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> P mem3 ->
    SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_END regs3 mem3 md3) (tp_QP P Q).

(* S0 (+0 -> +332 / +248 / +172): the prologue, the shadow base, the 4-byte check of t + 24 and the FAILED test
   (A0 goes straight to the epilogue with the text's post body already true), the checks of t + 8 / t + 16, the
   need test. It runs before the realloc: its walk is plain and is lifted once, at the entry (YGcfRhLift.ra_rh_of_SRr) *)
Definition tp_seg_S0 : Prop :=
  forall Q D, tp_pre D -> tp_k1pre D -> tp_img ->
  tp_k_END Q D -> tp_k_FIT Q D -> tp_k_GROWR (wle' segs YGcfRehidePost.RZ_cf) Q D ->
  P (ms_mem (cfg_ms (tp_cfg0 D))) ->
  SRr' segs YGcfRehidePost.RZ_cf (tp_W D) (tp_cfg0 D) (tp_QP P Q).
(* S_GROW (+172 -> +248): the load check of t, the realloc wrapper call (cap0 > 0: YGcallRkKeep.aj_realloc_at_x_cfR_keep
   over the primed keep row; cap0 = 0: YGcallRxKeep.aj_realloc_null_at_x_keep) at its admission (the kit's wild room),
   the NULL test - its NULL arm REFUTED (PRH_Refute.prh_refute_tx_put, by the kit's consumer window) - and the two stores
   of t->b and t->cap *)
Definition tp_seg_GROW : Prop :=
  forall Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  tp_at_GROW D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> tp_img ->
  tp_k_FIT Q D -> P mem3 ->
  SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_GROW regs3 mem3 md3) (tp_QP P Q).
(* S_FIT (+248 -> +332): the two load checks, __asan_memcpy (b1 + len0, s, n), t->n := len0 + n, the 1-byte store
   check and the NUL store; the DONE post body at the end state *)
Definition tp_seg_FIT : Prop :=
  forall Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1,
  tp_at_FIT D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 -> tp_img ->
  tp_k_END Q D -> P mem3 ->
  SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_FIT regs3 mem3 md3) (tp_QP P Q).
(* S_END (+332 -> ret): the thirteen restores, `addi sp, sp, 112` and ret; the text's caller-window post *)
Definition tp_seg_END : Prop :=
  forall D ly3 S3 Hp3 W3 regs3 mem3 md3 k,
  tp_at_END D ly3 S3 Hp3 W3 regs3 mem3 md3 k -> tp_img -> P mem3 ->
  SRr' segs YGcfRehidePost.RZ_cf W3 (tp_cfg TP_PC_END regs3 mem3 md3) (tp_QP P (tp_text_postW D)).
End segs.

(* ---- THE GROW ROW'S CLOSING STATEMENT (owner's ruling 15:4xZ on a finding, BOTH images; the same names and
   order as lib/B/Prog/TxPut102B_Base.v): the realloc WRAPPER's callee texts, the primed keep row
   YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep (every headroom k) and
   YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep at the listing's own entry SIGMA AS___wrap_realloc, are named
   premises of the statement, BEFORE P (the rows with the memnorm keep: the walk carries P across the call by
   srr_inv_call, which reads the leaf's keep). TxPut102A_Top.v / TxPut102A_Inst.v take them as named Variables,
   discharged at the instance by AllocAssembleA.arealloc_realizes_cf_A / arealloc_null_realizes_cf_A
   (lib/A/AllocAssembleA.v:58, :91). With them, ARX_DEPOT: the depot of every ARcfx state has no repeats, which the batch kit admission
   at the call needs (YCbqGwild.ajournal_xw_admits's NoDup premise). It is AR_laws_x's field 25 (YCbqG.v
   ARx_depot_nodup_law) at ARcfx: the statement keeps it as a binder, and TxPut102A_Inst.v gives it as the field's
   projection alx_depot_nodup of the cf laws. ---- *)
Definition tp_AREAL : Prop :=
  forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep segs B Hp (SIGMA AS___wrap_realloc) k.
Definition tp_AREALN : Prop :=
  forall Hp, YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep segs B Hp (SIGMA AS___wrap_realloc).
Definition tp_ARX_DEPOT : Prop := forall ly S Hp W mem md, ARcfx ly S Hp W mem md -> List.NoDup (st_depot S).
Definition tp_seg_GROW_stmt : Prop :=
  forall (AREAL : forall Hp k, YGcfInstReallocKKeep.arealloc_realizes_cf_k_keep segs B Hp (SIGMA AS___wrap_realloc) k)
         (AREALN : forall Hp, YGcfReallocComposeKeep.arealloc_null_realizes_cf_keep segs B Hp (SIGMA AS___wrap_realloc))
         (ARX_DEPOT : forall ly S Hp W mem md, ARcfx ly S Hp W mem md -> List.NoDup (st_depot S))
         (P : (word -> option byte) -> Prop),
  srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_GROW P.

(* the instantiation at the top: the memnorm keep from the entry memory (YSRrMemnorm's carriers) pays fpostWm's
   memnorm conjunct *)
Definition tp_mn (D : tp_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm segs (tp_mem D) -> YAkMemnorm.memnorm segs m.
Lemma tp_mn_laws : forall D, srr_inv_laws segs (tp_mn D).
Proof. intros D. exact (srr_inv_laws_imp segs (YAkMemnorm.memnorm segs) (tp_mem D) (srr_inv_laws_memnorm_k segs)). Qed.
Lemma tp_mn_call : forall D, srr_inv_call segs (tp_mn D).
Proof. intros D. exact (srr_inv_call_imp segs (tp_mem D)). Qed.
Lemma tp_mn_refl : forall D, tp_mn D (tp_mem D).
Proof. intros D H. exact H. Qed.
End tp.

Print Assumptions tp_text_of_walk.
Print Assumptions tp_J_R_wle.
Print Assumptions tp_carry_R_wle.
